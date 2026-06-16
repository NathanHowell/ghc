{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE Unsafe #-}

{-# OPTIONS_GHC #-}
{-# OPTIONS_HADDOCK not-home #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Internal.Conc.STM
-- Copyright   :  (c) The University of Glasgow, 1994-2002
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  ghc-devs@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC extensions)
--
-- STM implementation details.
--
-- == The plan-based applicative STM, in brief
--
-- @STM a@ is an executable AST ('STMPlan'): @Applicative@ builds 'SApp'
-- fragments, @Monad@ sequencing builds 'SBind', and the control-flow
-- combinators ('retry', 'orElse', 'throwSTM', 'catchSTM', 'unsafeIOToSTM',
-- 'mfixSTM') each emit a dedicated node.  'atomically' interprets the
-- plan in @IO@ against an /immutable/ transaction log, yielding one of three
-- outcomes ('STMOutcome': @Ok@, @Retry@, @Raise@), then commits/blocks/rethrows
-- against the RTS.
--
-- == Two immutable lists, not one mutable SoA log
--
-- The log is split into two persistent (cons-front) association lists; see
-- @rts/STM-free-applicative.md@ \"The elegant target\".
--
--   * 'txLog' — the reads /and/ writes the transaction has performed.  Rolled
--     back by /both/ 'orElse' (discard a branch) and 'catchSTM' (forget a
--     caught body) simply by handing the alternative the captured prior list.
--     Used only on the @Ok@ path: marshalled (and de-duplicated) into arrays
--     for 'stmCommitLog#'.
--
--   * 'txWait' — a /monotone/, reads-only wait set.  An 'orElse' branch extends
--     it even when that branch is discarded (so a full @retry@ waits on the
--     union of every branch's reads), but 'catchSTM' rolls it back with the
--     body.  Used only on the @Retry@ path: registered exactly once, in
--     'runAtomically', via 'registerLogRange#'.
--
-- Splitting the two roles is what lets registration happen exactly once at the
-- top (no mid-flight @clearRegistrations#@ churn, no @RetryWithWait@ outcome,
-- no @differenceTxLog@): nothing can clobber a sibling 'orElse' branch's
-- registration because nothing registers until the whole transaction retries.
--
-- Both lists insert by /consing to the front/ (O(1), no spine rebuild) and look
-- up by /first match/; de-duplication is deferred to the single commit
-- marshalling pass.  Lengths are tracked incrementally so the marshalling pass
-- needs no separate @length@ traversal.
--
-- == Validation
--
-- Reads are taken from live memory at access time, so between two reads the
-- interpreter can be running arbitrary user code over a mutually-inconsistent
-- snapshot.  'validateLog' (the lock-free 'validate#' primop over the read set)
-- is called before a potentially-divergent continuation ('SBind') and at the
-- top-level @Retry@.  A mid-flight mismatch abandons the current attempt as a
-- @Retry@; 'runAtomically' re-validates the wait set before blocking, so an
-- invalidated (\"zombie\") transaction restarts immediately instead of blocking,
-- while a genuine @retry@ blocks.  Commit-time validation in 'stmCommitLog#' is
-- the backstop that makes this safe even when the mid-flight check is skipped.
--
-----------------------------------------------------------------------------

module GHC.Internal.Conc.STM
        ( STM
        , mfixSTM
        , atomically
        , retry
        , orElse
        , throwSTM
        , catchSTM
        , TVar(..)
        , newTVar
        , newTVarIO
        , readTVar
        , readTVarIO
        , writeTVar
        , unsafeIOToSTM
        ) where

#include "MachDeps.h"

import GHC.Internal.Base
import GHC.Internal.Exception
import GHC.Internal.List (any, length)
import GHC.Internal.Num
import GHC.Internal.Unsafe.Coerce (unsafeCoerce#)
-- Upstream's "Refine GHC.Internal.Base imports" (6f4f6cf03a) slimmed Base's
-- re-export of GHC.Internal.Prim, so import the primitive types/classes directly.
import GHC.Internal.Prim
import GHC.Internal.Types ( IO(..), Bool(..), Int(..), Any, isTrue# )
import GHC.Internal.Classes ( Eq(..), Ord(..), not, (||) )
import GHC.Internal.Maybe ( Maybe(..) )
-- Explicit black-holing for SFix (mfix), reusing the fixIO/fixST shape.  These
-- modules sit below Conc.STM in the import graph (none depend on it), so there
-- is no cycle.  See 'evalFix'.
import GHC.Internal.IO ( catch, throwIO )
import GHC.Internal.MVar ( newEmptyMVar, readMVar, putMVar )
import GHC.Internal.IO.Unsafe ( unsafeDupableInterleaveIO )
import GHC.Internal.IO.Exception ( FixIOException(..), BlockedIndefinitelyOnMVar(..) )

-----------------------------------------------------------------------------
-- Transactional heap operations
-----------------------------------------------------------------------------

-- TVars are shared memory locations which support atomic memory
-- transactions.

-- | The executable plan that an @STM a@ denotes.  Control flow lives here;
-- 'STMPrim' nodes are the leaves that actually touch 'TVar's.  'Applicative'
-- combination keeps a maximal effect-free \"fragment\" in 'SApp' (so its read
-- and write sets are statically enumerable — the precondition for 'readMany#'
-- batching); any 'Monad' sequencing or control-flow
-- combinator drops to the corresponding dedicated constructor.
data STMPlan a where
  SPure :: a -> STMPlan a
  SPrim :: STMPrim a -> STMPlan a
  SApp :: STMPlan (a -> b) -> STMPrim a -> STMPlan b
  SBind :: STMPlan a -> (a -> STMPlan b) -> STMPlan b
  SRetry :: STMPlan a
  SOrElse :: STMPlan a -> STMPlan a -> STMPlan a
  SThrow :: SomeException -> STMPlan a
  SCatch :: STMPlan a -> (SomeException -> STMPlan a) -> STMPlan a
  SUnsafeIO :: IO a -> STMPlan a
  SFix :: (a -> STMPlan a) -> STMPlan a

data STMPrim a where
  PRead :: TVar a -> STMPrim a
  PWrite :: TVar a -> a -> STMPrim ()
  PNewTVar :: a -> STMPrim (TVar a)

newtype STM a = STM
  { stmPlan :: STMPlan a
  }

planMap :: (a -> b) -> STMPlan a -> STMPlan b
planMap f plan = case plan of
  SPure a -> SPure (f a)
  SPrim p -> SApp (SPure f) p
  SApp pf px -> SApp (planMap (f .) pf) px
  SBind p k -> SBind p (\a -> planMap f (k a))
  SRetry -> SRetry
  SOrElse l r -> SOrElse (planMap f l) (planMap f r)
  SThrow e -> SThrow e
  SCatch p h -> SCatch (planMap f p) (\e -> planMap f (h e))
  SUnsafeIO io -> SBind (SUnsafeIO io) (\a -> SPure (f a))
  SFix k -> SBind (SFix k) (\a -> SPure (f a))

planApply :: STMPlan (a -> b) -> STMPlan a -> STMPlan b
planApply pf px = case px of
  SPure x -> planMap ($ x) pf
  SPrim p -> SApp pf p
  SApp inner p -> SApp (planApply (planMap (.) pf) inner) p
  _ -> SBind pf (\f -> SBind px (\x -> SPure (f x)))

-- | A single log entry: @(tvar, expected, new)@.  @expected@ is the value read
-- from live memory at first access; @new@ is the value read or last written.
-- @expected == new@ (pointer equality) marks a read-only entry.
--
-- The existential + 'unsafeCoerce#' is inherent at this layer (below
-- @containers@): a heterogeneous @TVar a -> (a, a)@ map cannot be expressed
-- otherwise.  The value coercions are confined to 'logLookup'\/'reads' and rely
-- on the per-transaction invariant that a given 'TVar' is always stored at the
-- single type it was created with (see 'sameTVar' — keyed purely on address).
data TxEntry where
  TxEntry :: TVar a -> a -> a -> TxEntry

-- | A wait-set entry: @(tvar, expected)@.  Reads-only; the wait set never
-- carries write targets, so write-only 'TVar's are never registered as waiters.
data WaitEntry where
  WaitEntry :: TVar a -> a -> WaitEntry

-- Entries are (tvar, expected, new).  Immutable, cons-front; at most one
-- /logical/ entry per TVar after de-duplication at the commit boundary.
type TxLog = [TxEntry]

-- Reads-only, monotone, cons-front.
type WaitSet = [WaitEntry]

-- | The transaction state threaded through the interpreter.  Two immutable
-- lists (see the module header), each with an incrementally-tracked length so
-- marshalling needs no @length@ pass.
data TxState = TxState
  { txLog     :: TxLog    -- reads + writes; rolled back by orElse and catchSTM
  , txLogLen  :: !Int     -- length of txLog (upper bound; pre-dedup)
  , txWait    :: WaitSet  -- monotone reads-only wait set
  , txWaitLen :: !Int     -- length of txWait (upper bound; pre-dedup)
  }

-- The three-outcome model (Ok | Retry | Raise).  A mid-flight validation
-- failure is reported as Retry; runAtomically re-validates before blocking, so
-- an invalidated transaction restarts immediately rather than blocking.
data STMOutcome a = Ok a | Retry | Raise SomeException

emptyTxState :: TxState
emptyTxState = TxState [] 0 [] 0

sameTVar :: TVar a -> TVar b -> Bool
sameTVar (TVar tv1#) (TVar tv2#) =
  isTrue# (eqAddr# (unsafeCoerce# tv1#) (unsafeCoerce# tv2#))

-- | Coerce a logged value back to the accessor's type.  Sound by the
-- per-transaction fixed-type invariant documented on 'TxEntry': every entry for
-- a given 'TVar' was written\/read at the one type the 'TVar' holds.  This is
-- the /single/ place value coercion happens on the read path.
coerceVal :: a -> b
coerceVal = unsafeCoerce#
{-# INLINE coerceVal #-}

-- Like Prelude.lookup, but specialised for the TxLog association list and
-- returning the most-recent (front-most) entry.  O(1) amortised on the common
-- hit; linear on a miss.  Linear lookup is irreducible for a list at this
-- layer, and is the only non-constant operation now that insert is cons-front.
logLookup :: TVar a -> TxLog -> Maybe (a, a)
logLookup _ [] = Nothing
logLookup tv (TxEntry tv' expected newVal : rest)
  | sameTVar tv tv' = Just (coerceVal expected, coerceVal newVal)
  | otherwise = logLookup tv rest

stateToIO :: (State# RealWorld -> (# State# RealWorld, a #)) -> IO a
stateToIO = IO
{-# INLINE stateToIO #-}

stateToIO_ :: (State# RealWorld -> State# RealWorld) -> IO ()
stateToIO_ f = IO $ \s0 -> (# f s0, () #)
{-# INLINE stateToIO_ #-}

atomicallyIO :: IO a -> IO a
atomicallyIO (IO m) = stateToIO (atomically# m)
{-# INLINE atomicallyIO #-}

raiseIOIO :: SomeException -> IO a
raiseIOIO e = stateToIO (raiseIO# e)
{-# INLINE raiseIOIO #-}

catchSTMIO :: IO a -> (SomeException -> IO a) -> IO a
catchSTMIO (IO m) handler =
  stateToIO $ \s0 ->
    catch# m (\e s -> case handler (unsafeCoerce# e) of IO m' -> m' s) s0
{-# INLINE catchSTMIO #-}

blockOnRegisteredIO :: IO ()
blockOnRegisteredIO = stateToIO_ $ \s0 ->
  case blockOnRegistered# s0 of
    (# s1, _ #) -> s1
{-# INLINE blockOnRegisteredIO #-}

-- A lifted box for the unlifted SmallMutableArray#, so it can be returned from
-- IO (whose result kind must be lifted). Cf. "STM: avoid IO with unlifted results".
data MutArr = MutArr (SmallMutableArray# RealWorld Any)

-- | The array placeholder.  Genuinely bottom: every slot is overwritten before
-- the array is handed to a primop, so a stray read of an un-filled slot is a
-- bug — make it fault loudly rather than return a silently-wrong 'Any' (L-6).
emptyAny :: Any
emptyAny = raise# (errorCallException "GHC.Internal.Conc.STM: uninitialised log slot")
{-# NOINLINE emptyAny #-}

newSmallArrayIO :: Int -> Any -> IO MutArr
newSmallArrayIO (I# n#) initVal = IO $ \s0 ->
  case newSmallArray# n# initVal s0 of
    (# s1, arr #) -> (# s1, MutArr arr #)

writeSmallArrayIO :: SmallMutableArray# RealWorld Any -> Int -> Any -> IO ()
writeSmallArrayIO arr (I# i#) val = stateToIO_ (writeSmallArray# arr i# val)

readSmallArrayIO :: SmallMutableArray# RealWorld Any -> Int -> IO Any
readSmallArrayIO arr (I# i#) = stateToIO (readSmallArray# arr i#)

registerLogRangeArraysIO
  :: SmallMutableArray# RealWorld Any
  -> SmallMutableArray# RealWorld Any
  -> Int
  -> Int
  -> IO ()
registerLogRangeArraysIO tvars expected (I# start#) (I# end#) =
  stateToIO_ (registerLogRange# tvars expected start# end#)

stmCommitLogArraysIO
  :: SmallMutableArray# RealWorld Any
  -> SmallMutableArray# RealWorld Any
  -> SmallMutableArray# RealWorld Any
  -> Int
  -> IO Int
stmCommitLogArraysIO tvars expected new (I# len#) =
  stateToIO $ \s0 ->
    case stmCommitLog# tvars expected new len# s0 of
      (# s1, result# #) -> (# s1, I# result# #)

validateArraysIO
  :: SmallMutableArray# RealWorld Any
  -> SmallMutableArray# RealWorld Any
  -> Int
  -> IO Int
validateArraysIO tvars expected (I# len#) =
  stateToIO $ \s0 ->
    case validate# tvars expected len# s0 of
      (# s1, result# #) -> (# s1, I# result# #)

readManyArraysIO
  :: SmallMutableArray# RealWorld Any
  -> SmallMutableArray# RealWorld Any
  -> SmallMutableArray# RealWorld Any
  -> Int
  -> IO Int
readManyArraysIO tvars results expected (I# len#) =
  stateToIO $ \s0 ->
    case readMany# tvars results expected len# s0 of
      (# s1, result# #) -> (# s1, I# result# #)

-----------------------------------------------------------------------------
-- Marshalling the immutable lists to primop arrays (the one place the spine is
-- walked).  De-duplication happens here, keeping only the most-recent (front)
-- entry per TVar; everything upstream cons-es freely.
-----------------------------------------------------------------------------

-- | Marshal a 'TxLog' into freshly-allocated @(tvars, expected, new)@ arrays,
-- de-duplicating to the front-most entry per 'TVar'.  Returns the boxed arrays
-- and the de-duplicated length.  @lenHint@ is the incrementally-tracked upper
-- bound used to size the arrays.
marshalLog :: TxLog -> Int -> IO (MutArr, MutArr, MutArr, Int)
marshalLog log lenHint = do
  MutArr tvars <- newSmallArrayIO lenHint emptyAny
  MutArr expected <- newSmallArrayIO lenHint emptyAny
  MutArr new <- newSmallArrayIO lenHint emptyAny
  let go _ [] = return (MutArr tvars, MutArr expected, MutArr new, 0)
      go i (TxEntry (TVar tv#) expectedVal newVal : rest) = do
        -- Cons-front means the first occurrence is the most recent; a TVar
        -- already emitted (closer to the front) shadows this older entry.
        already <- tvarSeen tvars i (unsafeCoerce# tv#)
        if already
          then go i rest
          else do
            writeSmallArrayIO tvars i (unsafeCoerce# tv#)
            writeSmallArrayIO expected i (unsafeCoerce# expectedVal)
            writeSmallArrayIO new i (unsafeCoerce# newVal)
            (a, b, c, n) <- go (i + 1) rest
            return (a, b, c, n + 1)
  go 0 log

-- | Marshal a reads-only 'WaitSet' into @(tvars, expected)@ arrays, de-duped.
marshalWait :: WaitSet -> Int -> IO (MutArr, MutArr, Int)
marshalWait waits lenHint = do
  MutArr tvars <- newSmallArrayIO lenHint emptyAny
  MutArr expected <- newSmallArrayIO lenHint emptyAny
  let go _ [] = return (MutArr tvars, MutArr expected, 0)
      go i (WaitEntry (TVar tv#) expectedVal : rest) = do
        already <- tvarSeen tvars i (unsafeCoerce# tv#)
        if already
          then go i rest
          else do
            writeSmallArrayIO tvars i (unsafeCoerce# tv#)
            writeSmallArrayIO expected i (unsafeCoerce# expectedVal)
            (a, b, n) <- go (i + 1) rest
            return (a, b, n + 1)
  go 0 waits

-- | Marshal a reads-only 'WaitSet' into @(tvars, expected)@ arrays /without/
-- de-duplication, in a single O(n) pass.  Used only for validation, where a
-- duplicate TVar just costs a redundant (harmless) pointer compare: skipping the
-- O(n)-per-entry 'tvarSeen' dedup scan turns each validation from O(n²) into
-- O(n), which is what keeps a long orElse/bind chain (e.g. #26028's 50k-branch
-- @foldr1 orElse@) from going cubic overall.  @lenHint@ must be an upper bound on
-- the spine length.
marshalWaitNoDedup :: WaitSet -> Int -> IO (MutArr, MutArr, Int)
marshalWaitNoDedup waits lenHint = do
  MutArr tvars <- newSmallArrayIO lenHint emptyAny
  MutArr expected <- newSmallArrayIO lenHint emptyAny
  let go i [] = return (MutArr tvars, MutArr expected, i)
      go i (WaitEntry (TVar tv#) expectedVal : rest) = do
        writeSmallArrayIO tvars i (unsafeCoerce# tv#)
        writeSmallArrayIO expected i (unsafeCoerce# expectedVal)
        go (i + 1) rest
  go 0 waits

-- Has this TVar pointer already been written into tvars[0..count)?  Uses the
-- levity-polymorphic, hetero-typed 'reallyUnsafePtrEquality#' for direct boxed
-- pointer identity (the stored 'Any' is a coerced 'TVar#'); no cross-rep
-- 'Addr#' reinterpretation needed.
tvarSeen :: SmallMutableArray# RealWorld Any -> Int -> Any -> IO Bool
tvarSeen arr count target = loop 0
  where
    loop i
      | i == count = return False
      | otherwise = do
          v <- readSmallArrayIO arr i
          if isTrue# (reallyUnsafePtrEquality# v target)
            then return True
            else loop (i + 1)

-----------------------------------------------------------------------------
-- Commit / validate / register against the RTS.
-----------------------------------------------------------------------------

commitTxLog :: TxLog -> Int -> IO Bool
commitTxLog [] _ = return True
commitTxLog log lenHint = do
  (MutArr tvars, MutArr expected, MutArr new, n) <- marshalLog log lenHint
  result <- stmCommitLogArraysIO tvars expected new n
  return (result == 0)

-- | Register the whole monotone wait set on the RTS wait queues, exactly once.
registerWaitSet :: WaitSet -> Int -> IO ()
registerWaitSet [] _ = return ()
registerWaitSet waits lenHint = do
  (MutArr tvars, MutArr expected, n) <- marshalWait waits lenHint
  registerLogRangeArraysIO tvars expected 0 n

-- | Lock-free validate the reads-only wait set.  'True' if still consistent.
-- Uses the non-deduping marshal: 'validate#' tolerates (and a repeated read is
-- idempotent for) duplicate TVars, so we avoid the quadratic dedup scan.
validateWaitSet :: WaitSet -> Int -> IO Bool
validateWaitSet [] _ = return True
validateWaitSet waits lenHint = do
  (MutArr tvars, MutArr expected, n) <- marshalWaitNoDedup waits lenHint
  result <- validateArraysIO tvars expected n
  return (result == 0)

-- | Validate the current transaction's read set before a potentially-divergent
-- continuation (C-2).  We validate the wait set, which is exactly the set of
-- live-memory reads.  'True' if still consistent.
validateTx :: TxState -> IO Bool
validateTx st = validateWaitSet (txWait st) (txWaitLen st)

-----------------------------------------------------------------------------
-- Logged TVar access.
-----------------------------------------------------------------------------

-- | Read a 'TVar' through the log.  A hit returns the logged @new@ value and
-- records no new dependency (the dependency, if any, was captured when the
-- entry's @expected@ was first established).  A miss reads live memory, conses
-- a read-only entry onto 'txLog' /and/ a @(tvar, value)@ entry onto the monotone
-- 'txWait' (this is the only place the wait set grows — keeping it exactly the
-- set of live-memory reads, never write-only TVars).
readTVarTx :: TxState -> TVar a -> IO (a, TxState)
readTVarTx st tv =
  case logLookup tv (txLog st) of
    Just (_, newVal) ->
      return (newVal, st)
    Nothing -> do
      val <- readTVarIO tv
      let st' = st
            { txLog     = TxEntry tv val val : txLog st
            , txLogLen  = txLogLen st + 1
            , txWait    = WaitEntry tv val : txWait st
            , txWaitLen = txWaitLen st + 1
            }
      return (val, st')

-- | Write a 'TVar' through the log.  On a hit, cons a fresh entry carrying the
-- /original/ @expected@ and the new value (front-most wins at marshalling, so
-- this is last-write-wins without rewriting the spine).  On a miss, read live
-- memory for @expected@.  Writes never touch the wait set (write-only TVars are
-- not waited on).
writeTVarTx :: TxState -> TVar a -> a -> IO TxState
writeTVarTx st tv val =
  case logLookup tv (txLog st) of
    Just (expected, _) ->
      return st
        { txLog    = TxEntry tv expected val : txLog st
        , txLogLen = txLogLen st + 1
        }
    Nothing -> do
      expected <- readTVarIO tv
      return st
        { txLog    = TxEntry tv expected val : txLog st
        , txLogLen = txLogLen st + 1
        }

evalPrim :: TxState -> STMPrim a -> IO (a, TxState)
evalPrim st prim = case prim of
  PRead tv -> readTVarTx st tv
  PWrite tv val -> do
    st' <- writeTVarTx st tv val
    return ((), st')
  PNewTVar val -> do
    tv <- newTVarIO val
    return (tv, st)

-----------------------------------------------------------------------------
-- Applicative-fragment static analysis (for readMany# batching).  A "fragment"
-- is any plan built solely from SPure / SApp / SPrim: its read set is
-- statically enumerable with no intervening control flow.
-----------------------------------------------------------------------------

-- | Collect the 'PRead' 'TVar's of a pure applicative fragment in evaluation
-- order, or 'Nothing' if the plan contains control flow (so the read set is not
-- statically known).  We existentially erase the element type — only the
-- address matters for batching.
fragmentReads :: STMPlan a -> Maybe [SomeTV]
fragmentReads = go []
  where
    go :: [SomeTV] -> STMPlan b -> Maybe [SomeTV]
    go acc (SPure _) = Just acc
    go acc (SPrim p) = prim acc p
    go acc (SApp pf p) = do
      acc' <- prim acc p
      go acc' pf
    go _ _ = Nothing

    prim :: [SomeTV] -> STMPrim b -> Maybe [SomeTV]
    prim acc (PRead tv) = Just (SomeTV tv : acc)
    prim acc (PWrite _ _) = Just acc
    prim acc (PNewTVar _) = Just acc

data SomeTV where
  SomeTV :: TVar a -> SomeTV

-- | Batch-read a fragment's read set with 'readMany#' and fold the snapshot
-- into 'txLog'\/'txWait', then evaluate the fragment against the now-populated
-- log (each 'PRead' becomes a hit; writes proceed normally).  Returns 'Nothing'
-- and leaves the state untouched if the batch observed a concurrent commit
-- (caller restarts the fragment) — but only attempts the batch for fragments
-- with at least two distinct reads, where it pays off.
tryReadMany :: TxState -> STMPlan a -> IO (Maybe (STMOutcome a, TxState))
tryReadMany st plan =
  case fragmentReads plan of
    Just reads@(_ : _ : _)
      -- 'readMany#' reads live memory.  A TVar this transaction has already
      -- logged (read or written) carries a value the batch read would miss, so
      -- when any fragment read is already resolvable from the log, fall back to
      -- per-read evaluation ('evalApp' -> 'readTVarTx'), which serves those from
      -- the snapshot.
      | any (\(SomeTV tv) -> readResolvable tv st) reads ->
          return Nothing
      | otherwise -> do
          let n = length reads
          MutArr tvars <- newSmallArrayIO n emptyAny
          MutArr results <- newSmallArrayIO n emptyAny
          MutArr expected <- newSmallArrayIO n emptyAny
          let fill _ [] = return ()
              fill i (SomeTV (TVar tv#) : rest) = do
                writeSmallArrayIO tvars i (unsafeCoerce# tv#)
                fill (i + 1) rest
          fill 0 reads
          rc <- readManyArraysIO tvars results expected n
          if rc /= 0
            then return Nothing
            else do
              st' <- foldReads st 0 n tvars results
              (out, st'') <- evalFragment st' plan
              return (Just (out, st''))
    _ -> return Nothing

-- | Is a read of this 'TVar' resolvable from the current transaction state
-- without touching live memory — i.e. already in the log?  Such TVars must be
-- served by 'readTVarTx', never batched through 'readMany#' (which reads live
-- memory and would miss an earlier logged write).
readResolvable :: TVar a -> TxState -> Bool
readResolvable tv st = logged (txLog st)
  where
    logged []                      = False
    logged (TxEntry tv' _ _ : rest) = sameTVar tv tv' || logged rest

-- Fold a readMany# result batch into the log and monotone wait set.  Each TVar
-- becomes a read-only log entry and a wait entry (skipping addresses already
-- logged, preserving the "exactly the live-memory reads" wait-set invariant and
-- first-match semantics).
foldReads
  :: TxState
  -> Int -> Int
  -> SmallMutableArray# RealWorld Any
  -> SmallMutableArray# RealWorld Any
  -> IO TxState
foldReads st i n tvars results
  | i == n = return st
  | otherwise = do
      tvAny <- readSmallArrayIO tvars i
      valAny <- readSmallArrayIO results i
      let tv = anyToTVar tvAny
      case logLookup tv (txLog st) of
        Just _ -> foldReads st (i + 1) n tvars results
        Nothing -> do
          let val = coerceVal valAny
              st' = st
                { txLog     = TxEntry tv val val : txLog st
                , txLogLen  = txLogLen st + 1
                , txWait    = WaitEntry tv val : txWait st
                , txWaitLen = txWaitLen st + 1
                }
          foldReads st' (i + 1) n tvars results

anyToTVar :: Any -> TVar a
anyToTVar a = TVar (unsafeCoerce# a)
{-# INLINE anyToTVar #-}

-- Evaluate a pure applicative fragment whose reads are already in the log
-- (every PRead is a hit).  Mirrors the SApp/SPrim/SPure arms of evalSTM but
-- without re-attempting readMany# (avoiding nontermination).
evalFragment :: TxState -> STMPlan a -> IO (STMOutcome a, TxState)
evalFragment st plan = case plan of
  SPure a -> return (Ok a, st)
  SPrim p -> do
    (a, st') <- evalPrim st p
    return (Ok a, st')
  SApp pf px -> do
    (outcome, st') <- evalFragment st pf
    case outcome of
      Ok f -> do
        (x, st'') <- evalPrim st' px
        return (Ok (f x), st'')
      Retry -> return (Retry, st')
      Raise e -> return (Raise e, st')
  _ -> evalSTM st plan  -- not actually a fragment; defensive fall-through

-----------------------------------------------------------------------------
-- The interpreter.
-----------------------------------------------------------------------------

evalSTM :: TxState -> STMPlan a -> IO (STMOutcome a, TxState)
evalSTM st plan = case plan of
  SPure a -> return (Ok a, st)
  SPrim p -> do
    (a, st') <- evalPrim st p
    return (Ok a, st')
  SApp _ _ -> do
    -- Try a batched read of the whole fragment first; fall back to one-at-a-
    -- time evaluation if it isn't profitable or observed a concurrent commit.
    mb <- tryReadMany st plan
    case mb of
      Just res -> return res
      Nothing -> evalApp st plan
  SBind p k -> do
    (outcome, st') <- evalSTM st p
    case outcome of
      Ok a -> do
        -- C-2: validate the read set before running the (arbitrary,
        -- potentially-divergent) continuation.  A stale snapshot abandons the
        -- attempt as Retry; runAtomically re-validates and restarts immediately.
        consistent <- validateTx st'
        if consistent
          then evalSTM st' (k a)
          else return (Retry, st')
      Retry -> return (Retry, st')
      Raise e -> return (Raise e, st')
  SRetry ->
    return (Retry, st)
  SOrElse left right -> do
    (outcomeL, stL) <- evalSTM st left
    case outcomeL of
      Ok a ->
        return (Ok a, stL)
      Raise e ->
        return (Raise e, stL)
      Retry -> do
        -- Roll the *log* (reads+writes) back to the entering state for the
        -- right branch, but carry the *monotone wait set* forward: stL.txWait
        -- already ⊇ the entering wait set plus the left branch's reads (we only
        -- ever cons), so handing it to the right branch yields the union with
        -- no diffing and no mid-flight registration.
        let st1 = st { txWait = txWait stL, txWaitLen = txWaitLen stL }
        evalSTM st1 right
  SThrow e ->
    return (Raise e, st)
  SCatch body handler -> do
    (outcome, stBody) <- evalSTM st body
    case outcome of
      Ok a -> return (Ok a, stBody)
      -- retry is not caught (legacy); the body's reads stay in the wait set so
      -- a top-level retry waits on them.
      Retry -> return (Retry, stBody)
      Raise e ->
        -- A caught exception forgets the body entirely: roll back *both* the
        -- log and the wait set to the entering state, then run the handler.
        evalSTM st (handler e)
  SUnsafeIO io ->
    catchSTMIO
      (do
        a <- io
        return (Ok a, st))
      (\e -> return (Raise e, st))
  SFix k -> evalFix st k

-- One-TVar-at-a-time evaluation of an applicative fragment (the readMany#
-- fall-back path).  Reads not already batched go through readTVarTx.
evalApp :: TxState -> STMPlan a -> IO (STMOutcome a, TxState)
evalApp st plan = case plan of
  SApp pf px -> do
    (outcome, st') <- evalApp st pf
    case outcome of
      Ok f -> do
        (x, st'') <- evalPrim st' px
        return (Ok (f x), st'')
      Retry -> return (Retry, st')
      Raise e -> return (Raise e, st')
  SPrim p -> do
    (a, st') <- evalPrim st p
    return (Ok a, st')
  SPure a -> return (Ok a, st)
  _ -> evalSTM st plan

-- | @mfix@ for STM.  Ties the knot inside the transaction, matching the legacy
-- @MonadFix STM@ semantics, but with /explicit/ black-holing (an MVar-free
-- analogue is impossible here, so we reuse the 'fixIO'\/'fixST' shape) rather
-- than the lazy @State#@ knot the old instance used.  The lazy knot is exactly
-- what @fixST@ abandoned in #15349: lazy black-holing can /re-run/ the
-- effectful body and duplicate its reads\/writes.  Here the body is interpreted
-- exactly once; the fixed-point value is forced lazily and, if demanded before
-- the body yields @Ok@, diverges into the black hole (raising
-- 'FixIOException'), preserving the legacy \"forcing diverges\" contract for
-- @retry@\/@throw@ outcomes.  See "GHC.Internal.Control.Monad.ST.Imp".
evalFix :: TxState -> (a -> STMPlan a) -> IO (STMOutcome a, TxState)
evalFix st k = do
  m <- newEmptyMVar
  ans <- unsafeDupableInterleaveIO
           (readMVar m `catch` \BlockedIndefinitelyOnMVar -> throwIO FixIOException)
  (out, st') <- evalSTM st (k ans)
  case out of
    Ok a -> do
      putMVar m a
      return (Ok a, st')
    Retry ->
      -- Leave m empty: forcing `ans` blocks indefinitely, the runtime detects
      -- the deadlock (BlockedIndefinitelyOnMVar) and we re-raise it as the
      -- standard 'FixIOException'.  This matches the legacy 'mfix' contract that
      -- a non-Ok body leaves the fixed point black-holed (forcing it diverges),
      -- but without the lazy-State#-knot re-run hazard of #15349.
      return (Retry, st')
    Raise e ->
      return (Raise e, st')

runAtomically :: STMPlan a -> IO a
runAtomically plan = go
  where
    go = do
      (outcome, st) <- evalSTM emptyTxState plan
      case outcome of
        Ok a -> do
          success <- commitTxLog (txLog st) (txLogLen st)
          if success
            then return a
            else go  -- commit conflict: stmCommitLog# already unlocked; restart
        Retry -> do
          -- C-2: re-validate the (reads-only) wait set before committing to a
          -- block.  An invalidated/zombie transaction (some logged read has
          -- since changed) restarts immediately; only a genuinely-consistent
          -- retry blocks on the union of every branch's reads.
          consistent <- validateWaitSet (txWait st) (txWaitLen st)
          if not consistent
            then go
            else do
              registerWaitSet (txWait st) (txWaitLen st)
              blockOnRegisteredIO
              go
        Raise e -> do
          raiseIOIO e

-----------------------------------------------------------------------------
-- MVar / interleave plumbing for evalFix (explicit black-holing, fixIO-style).
-- Imported directly to keep the module's low position in the import graph;
-- GHC.Internal.MVar / .IO.Unsafe / .IO.Exception do not depend on Conc.STM.
-----------------------------------------------------------------------------

instance Functor STM where
   fmap f (STM plan) = STM (planMap f plan)

-- | @since base-4.8.0.0
instance Applicative STM where
  {-# INLINE pure #-}
  {-# INLINE liftA2 #-}
  pure x = returnSTM x
  STM pf <*> STM px = STM (planApply pf px)
  liftA2 f x y = pure f <*> x <*> y

-- | @since base-4.3.0.0
instance  Monad STM  where
    {-# INLINE (>>=)  #-}
    m >>= k     = bindSTM m k
    (>>) = (*>)

-- | @since base-4.17.0.0
instance Semigroup a => Semigroup (STM a) where
    (<>) = liftA2 (<>)

-- | @since base-4.17.0.0
instance Monoid a => Monoid (STM a) where
    mempty = pure mempty

bindSTM :: STM a -> (a -> STM b) -> STM b
bindSTM (STM plan) k = STM (SBind plan (\a -> stmPlan (k a)))

returnSTM :: a -> STM a
returnSTM x = STM (SPure x)

mfixSTM :: (a -> STM a) -> STM a
mfixSTM k = STM (SFix (\a -> stmPlan (k a)))
{-# INLINE mfixSTM #-}

-- | Takes the first non-'retry'ing 'STM' action.
--
-- @since base-4.8.0.0
instance Alternative STM where
  empty = retry
  (<|>) = orElse

-- | Takes the first non-'retry'ing 'STM' action.
--
-- @since base-4.3.0.0
instance MonadPlus STM

-- | Unsafely performs IO in the STM monad.  Beware: this is a highly
-- dangerous thing to do.
--
--   * The STM implementation will often run transactions multiple
--     times, so you need to be prepared for this if your IO has any
--     side effects.
--
--   * The STM implementation will abort transactions that are known to
--     be invalid and need to be restarted.  This may happen in the middle
--     of `unsafeIOToSTM`, so make sure you don't acquire any resources
--     that need releasing (exception handlers are ignored when aborting
--     the transaction).  That includes doing any IO using Handles, for
--     example.  Getting this wrong will probably lead to random deadlocks.
--
--   * The transaction may have seen an inconsistent view of memory when
--     the IO runs.  Invariants that you expect to be true throughout
--     your program may not be true inside a transaction, due to the
--     way transactions are implemented.  Normally this wouldn't be visible
--     to the programmer, but using `unsafeIOToSTM` can expose it.
--
unsafeIOToSTM :: IO a -> STM a
unsafeIOToSTM io = STM (SUnsafeIO io)

-- | Perform a series of STM actions atomically.
--
-- Using 'atomically' inside an 'unsafePerformIO' or 'unsafeInterleaveIO'
-- subverts some of guarantees that STM provides. It makes it possible to
-- run a transaction inside of another transaction, depending on when the
-- thunk is evaluated. If a nested transaction is attempted, an exception
-- is thrown by the runtime. It is possible to safely use 'atomically' inside
-- 'unsafePerformIO' or 'unsafeInterleaveIO', but the typechecker does not
-- rule out programs that may attempt nested transactions, meaning that
-- the programmer must take special care to prevent these.
--
-- However, there are functions for creating transactional variables that
-- can always be safely called in 'unsafePerformIO'. See: 'newTVarIO',
-- 'Control.Concurrent.STM.TChan.newTChanIO',
-- 'Control.Concurrent.STM.TChan.newBroadcastTChanIO',
-- 'Control.Concurrent.STM.TQueue.newTQueueIO',
-- 'Control.Concurrent.STM.TBQueue.newTBQueueIO', and
-- 'Control.Concurrent.STM.TMVar.newTMVarIO'.
--
-- Using 'unsafePerformIO' inside of 'atomically' is also dangerous but for
-- different reasons. See 'unsafeIOToSTM' for more on this.

atomically :: STM a -> IO a
atomically (STM plan) =
  case fastPath plan of
    Just action -> atomicallyIO action
    Nothing -> atomicallyIO (runAtomically plan)
  where
    fastPath p = case p of
      SPure a -> Just (return a)
      SThrow e -> Just (raiseIOIO e)
      SPrim prim -> fastPrim id prim
      SApp (SPure f) prim -> fastPrim f prim
      _ -> Nothing

    fastPrim :: (a -> b) -> STMPrim a -> Maybe (IO b)
    fastPrim f prim = case prim of
      PRead (TVar tvar#) ->
        Just (do
          a <- readTVarIO (TVar tvar#)
          return (f a))
      PNewTVar val ->
        Just (do
          tvar <- newTVarIO val
          return (f tvar))
      PWrite tv val ->
        -- M-3: a lone single-TVar write is the most common trivial transaction
        -- (counters, flags, TMVar puts).  Commit it directly through the log
        -- machinery (one entry → one-element arrays → stmCommitLog#), retrying
        -- on conflict, with no fragment analysis or separate sort step.
        Just (fmap f (commitSingleWrite tv val))

-- | Commit a single @writeTVar@ as its own one-entry transaction, looping on
-- commit conflict.  Reads the current value for @expected@ on each attempt.
commitSingleWrite :: TVar a -> a -> IO ()
commitSingleWrite tv val = loop
  where
    loop = do
      expected <- readTVarIO tv
      success <- commitTxLog [TxEntry tv expected val] 1
      if success then return () else loop

-- | Retry execution of the current memory transaction because it has seen
-- values in 'TVar's which mean that it should not continue (e.g. the 'TVar's
-- represent a shared buffer that is now empty).  The implementation may
-- block the thread until one of the 'TVar's that it has read from has been
-- updated. (GHC only)
retry :: STM a
retry = STM SRetry

-- | Compose two alternative STM actions (GHC only).
--
-- If the first action completes without retrying then it forms the result of
-- the 'orElse'. Otherwise, if the first action retries, then the second action
-- is tried in its place. If both actions retry then the 'orElse' as a whole
-- retries.
orElse :: STM a -> STM a -> STM a
orElse (STM planA) (STM planB) = STM (SOrElse planA planB)

-- | A variant of 'throw' that can only be used within the 'STM' monad.
--
-- Throwing an exception in @STM@ aborts the transaction and propagates the
-- exception. If the exception is caught via 'catchSTM', only the changes
-- enclosed by the catch are rolled back; changes made outside of 'catchSTM'
-- persist.
--
-- If the exception is not caught inside of the 'STM', it is re-thrown by
-- 'atomically', and the entire 'STM' is rolled back.
--
-- Although 'throwSTM' has a type that is an instance of the type of 'throw', the
-- two functions are subtly different:
--
-- > throw e    `seq` x  ===> throw e
-- > throwSTM e `seq` x  ===> x
--
-- The first example will cause the exception @e@ to be raised,
-- whereas the second one won\'t.  In fact, 'throwSTM' will only cause
-- an exception to be raised when it is used within the 'STM' monad.
-- The 'throwSTM' variant should be used in preference to 'throw' to
-- raise an exception within the 'STM' monad because it guarantees
-- ordering with respect to other 'STM' operations, whereas 'throw'
-- does not.
throwSTM :: Exception e => e -> STM a
throwSTM e =
  let ex = toException e
  in STM (SThrow ex)

-- | Exception handling within STM actions.
--
-- @'catchSTM' m f@ catches any exception thrown by @m@ using 'throwSTM',
-- using the function @f@ to handle the exception. If an exception is
-- thrown, any changes made by @m@ are rolled back, but changes prior to
-- @m@ persist.
catchSTM :: Exception e => STM a -> (e -> STM a) -> STM a
catchSTM (STM plan) handler = STM plan'
  where
    plan' = SCatch plan handlerPlan
    handlerPlan e = case fromException e of
      Just e' -> stmPlan (handler e')
      Nothing -> SThrow e

-- |Shared memory locations that support atomic memory transactions.
data TVar a = TVar (TVar# RealWorld a)

-- | @since base-4.8.0.0
instance Eq (TVar a) where
        (TVar tvar1#) == (TVar tvar2#) =
          isTrue# (eqAddr# (unsafeCoerce# tvar1#) (unsafeCoerce# tvar2#))

-- | Create a new 'TVar' holding a value supplied
newTVar :: a -> STM (TVar a)
newTVar val = STM (SPrim (PNewTVar val))

-- | @IO@ version of 'newTVar'.  This is useful for creating top-level
-- 'TVar's using 'System.IO.Unsafe.unsafePerformIO', because using
-- 'atomically' inside 'System.IO.Unsafe.unsafePerformIO' isn't
-- possible.
newTVarIO :: a -> IO (TVar a)
newTVarIO val = stateToIO $ \s1# ->
  case newTVar# val s1# of
    (# s2#, tvar# #) -> (# s2#, TVar tvar# #)

-- | Return the current value stored in a 'TVar'.
-- This is equivalent to
--
-- >  readTVarIO = atomically . readTVar
--
-- but works much faster, because it doesn't perform a complete
-- transaction, it just reads the current value of the 'TVar'.
readTVarIO :: TVar a -> IO a
readTVarIO (TVar tvar#) = stateToIO (readTVarIO# tvar#)

-- |Return the current value stored in a 'TVar'.
readTVar :: TVar a -> STM a
readTVar tv = STM (SPrim (PRead tv))

-- |Write the supplied value into a 'TVar'.
writeTVar :: TVar a -> a -> STM ()
writeTVar tv val = STM (SPrim (PWrite tv val))
