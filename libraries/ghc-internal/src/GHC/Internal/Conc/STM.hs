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
-- == The log, split by access kind
--
-- The log is two persistent (cons-front) association lists, split by access
-- kind; see @rts/STM-free-applicative.md@ \"The elegant target\".
--
--   * 'txReads' — the 'TVar's read from live memory, each with the observed
--     value.  /Monotone/: never rolled back within an attempt.  This single
--     list plays all three read roles — it is the wait set (registered on a
--     @retry@), the mid-flight validation set, and the read-validation half of
--     commit.
--
--   * 'txWrites' — the 'TVar's written, each with its @expected@ (pre-write)
--     and new value.  Speculative: rolled back by /both/ 'orElse' (discard a
--     branch) and 'catchSTM' (forget a caught body), simply by restoring the
--     captured entering list.
--
-- Splitting by access kind is what makes the control-flow combinators cheap and
-- uniform.  'orElse' (left retries) and 'catchSTM' (body throws) both reduce to
-- /restore the entering writes, keep the monotone reads/ — two O(1) field
-- updates, no diffing, no spine rebuild (see Note [Discard writes, keep reads]).
-- It is also why registration happens exactly once at the top (no mid-flight
-- @clearRegistrations#@ churn, no @RetryWithWait@ outcome, no @differenceTxLog@):
-- the monotone read set already holds the union of every branch's reads, so
-- nothing registers until the whole transaction retries.
--
-- Both lists insert by /consing to the front/ (O(1), no spine rebuild) and look
-- up by /first match/; de-duplication is deferred to the single commit
-- marshalling pass (where writes shadow reads of the same 'TVar').  Lengths are
-- tracked incrementally so marshalling needs no separate @length@ traversal.
--
-- == Validation
--
-- Reads are taken from live memory at access time, so between two reads the
-- interpreter can be running arbitrary user code over a mutually-inconsistent
-- snapshot.  'validateTx' (the lock-free 'validate#' primop over 'txReads') is
-- called before a potentially-divergent continuation ('SBind') and at the
-- top-level @Retry@.  A mid-flight mismatch abandons the current attempt as a
-- @Retry@; 'runAtomically' re-validates the read set before blocking, so an
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

-- The existential + 'unsafeCoerce#' in both entry types is inherent at this
-- layer (below @containers@): a heterogeneous @TVar a -> ...@ map cannot be
-- expressed otherwise.  The value coercions are confined to 'writeLookup',
-- 'readLookup', and the marshallers, and rely on the per-transaction invariant
-- that a given 'TVar' is always stored at the single type it was created with
-- (see 'sameTVar' — keyed purely on address).

-- | A logged write: @(tvar, expected, new)@.  @expected@ is the value the
-- transaction first observed for the 'TVar' (read live, or carried from an
-- earlier entry); @new@ is the value written.  A no-op write has
-- @expected == new@.
data WriteEntry where
  WriteEntry :: TVar a -> a -> a -> WriteEntry

-- | A logged read: @(tvar, expected)@, where @expected@ is the value observed
-- in live memory.  The read set doubles as the wait set: the reads are exactly
-- the 'TVar's a blocked transaction waits on, and exactly the set validated for
-- consistency at commit and mid-flight.
data ReadEntry where
  ReadEntry :: TVar a -> a -> ReadEntry

-- Immutable, cons-front; at most one /logical/ entry per TVar after the commit
-- marshalling pass de-duplicates (writes shadow reads, newer shadows older).
type WriteSet = [WriteEntry]
type ReadSet  = [ReadEntry]

-- | The transaction state threaded through the interpreter.  The log is split
-- by access kind into two immutable cons-front lists (see the module header),
-- each with an incrementally-tracked length so marshalling needs no @length@
-- pass.  The split is what makes 'orElse' and 'catchSTM' O(1): both keep the
-- monotone reads and restore only the writes.
data TxState = TxState
  { txReads     :: ReadSet   -- monotone reads = wait set = read-validation set;
                             -- never rolled back within an attempt
  , txReadsLen  :: !Int      -- length of txReads (upper bound; pre-dedup)
  , txWrites    :: WriteSet  -- speculative writes; rolled back by orElse and catchSTM
  , txWritesLen :: !Int      -- length of txWrites (upper bound; pre-dedup)
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
-- per-transaction fixed-type invariant documented on the entry types: every
-- entry for a given 'TVar' was written\/read at the one type the 'TVar' holds.
-- This is
-- the /single/ place value coercion happens on the read path.
coerceVal :: a -> b
coerceVal = unsafeCoerce#
{-# INLINE coerceVal #-}

-- Front-most lookup in the write set, returning @(expected, new)@.  Linear on a
-- miss; O(1) amortised on the common hit.  Linear lookup is irreducible for a
-- heterogeneous association list at this layer, and is the only non-constant
-- operation now that insert is cons-front.
writeLookup :: TVar a -> WriteSet -> Maybe (a, a)
writeLookup _ [] = Nothing
writeLookup tv (WriteEntry tv' expected newVal : rest)
  | sameTVar tv tv' = Just (coerceVal expected, coerceVal newVal)
  | otherwise = writeLookup tv rest

-- Front-most lookup in the read set, returning the observed @expected@ value.
readLookup :: TVar a -> ReadSet -> Maybe a
readLookup _ [] = Nothing
readLookup tv (ReadEntry tv' expected : rest)
  | sameTVar tv tv' = Just (coerceVal expected)
  | otherwise = readLookup tv rest

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

-- | Marshal the write set followed by the read set into freshly-allocated
-- @(tvars, expected, new)@ arrays for 'stmCommitLog#', de-duplicating to one
-- entry per 'TVar'.  Writes are emitted first so that a written 'TVar' shadows
-- any read of it (the commit must apply the write, not merely validate the read
-- value); reads are then emitted as no-op entries (@expected == new@) so the
-- commit validates them without perturbing @num_updates@.  The running fill
-- index doubles as the de-duplicated count.  @writeHint@\/@readHint@ are the
-- incrementally-tracked upper bounds used to size the arrays.
marshalCommit :: WriteSet -> Int -> ReadSet -> Int -> IO (MutArr, MutArr, MutArr, Int)
marshalCommit writes writeHint reads readHint = do
  MutArr tvars    <- newSmallArrayIO (writeHint + readHint) emptyAny
  MutArr expected <- newSmallArrayIO (writeHint + readHint) emptyAny
  MutArr new      <- newSmallArrayIO (writeHint + readHint) emptyAny
  let goW i [] = goR i reads
      goW i (WriteEntry (TVar tv#) ex nv : rest) = do
        -- Cons-front means the first occurrence is the most recent; a TVar
        -- already emitted (closer to the front) shadows this older entry.
        already <- tvarSeen tvars i (unsafeCoerce# tv#)
        if already
          then goW i rest
          else do
            writeSmallArrayIO tvars i (unsafeCoerce# tv#)
            writeSmallArrayIO expected i (unsafeCoerce# ex)
            writeSmallArrayIO new i (unsafeCoerce# nv)
            goW (i + 1) rest
      goR i [] = return (MutArr tvars, MutArr expected, MutArr new, i)
      goR i (ReadEntry (TVar tv#) ex : rest) = do
        -- Skip if this TVar was already emitted — by a write (shadowed) or an
        -- earlier read of the same TVar.
        already <- tvarSeen tvars i (unsafeCoerce# tv#)
        if already
          then goR i rest
          else do
            writeSmallArrayIO tvars i (unsafeCoerce# tv#)
            writeSmallArrayIO expected i (unsafeCoerce# ex)
            writeSmallArrayIO new i (unsafeCoerce# ex)
            goR (i + 1) rest
  goW 0 writes

-- | Marshal the read set into @(tvars, expected)@ arrays, de-duped (front-most
-- per 'TVar').  Used to register the wait set.
marshalReads :: ReadSet -> Int -> IO (MutArr, MutArr, Int)
marshalReads reads lenHint = do
  MutArr tvars <- newSmallArrayIO lenHint emptyAny
  MutArr expected <- newSmallArrayIO lenHint emptyAny
  let go i [] = return (MutArr tvars, MutArr expected, i)
      go i (ReadEntry (TVar tv#) ex : rest) = do
        already <- tvarSeen tvars i (unsafeCoerce# tv#)
        if already
          then go i rest
          else do
            writeSmallArrayIO tvars i (unsafeCoerce# tv#)
            writeSmallArrayIO expected i (unsafeCoerce# ex)
            go (i + 1) rest
  go 0 reads

-- | Marshal the read set into @(tvars, expected)@ arrays /without/
-- de-duplication, in a single O(n) pass.  Used only for validation, where a
-- duplicate TVar just costs a redundant (harmless) pointer compare: skipping the
-- O(n)-per-entry 'tvarSeen' dedup scan turns each validation from O(n²) into
-- O(n), which is what keeps a long orElse/bind chain (e.g. #26028's 50k-branch
-- @foldr1 orElse@) from going cubic overall.  @lenHint@ must be an upper bound on
-- the spine length.
marshalReadsNoDedup :: ReadSet -> Int -> IO (MutArr, MutArr, Int)
marshalReadsNoDedup reads lenHint = do
  MutArr tvars <- newSmallArrayIO lenHint emptyAny
  MutArr expected <- newSmallArrayIO lenHint emptyAny
  let go i [] = return (MutArr tvars, MutArr expected, i)
      go i (ReadEntry (TVar tv#) ex : rest) = do
        writeSmallArrayIO tvars i (unsafeCoerce# tv#)
        writeSmallArrayIO expected i (unsafeCoerce# ex)
        go (i + 1) rest
  go 0 reads

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

-- | Commit the transaction: validate the read set and validate-then-apply the
-- write set, all in one sorted 'stmCommitLog#' pass.  'True' on success.  An
-- all-empty transaction commits trivially; a read-only transaction (no writes)
-- still goes through the pass so its reads are validated.
commitTx :: WriteSet -> Int -> ReadSet -> Int -> IO Bool
commitTx [] _ [] _ = return True
commitTx writes writeHint reads readHint = do
  (MutArr tvars, MutArr expected, MutArr new, n) <-
    marshalCommit writes writeHint reads readHint
  result <- stmCommitLogArraysIO tvars expected new n
  return (result == 0)

-- | Register the whole monotone read set on the RTS wait queues, exactly once.
registerReads :: ReadSet -> Int -> IO ()
registerReads [] _ = return ()
registerReads reads lenHint = do
  (MutArr tvars, MutArr expected, n) <- marshalReads reads lenHint
  registerLogRangeArraysIO tvars expected 0 n

-- | Lock-free validate the read set.  'True' if still consistent.  Uses the
-- non-deduping marshal: 'validate#' tolerates (and a repeated read is idempotent
-- for) duplicate TVars, so we avoid the quadratic dedup scan.
validateReads :: ReadSet -> Int -> IO Bool
validateReads [] _ = return True
validateReads reads lenHint = do
  (MutArr tvars, MutArr expected, n) <- marshalReadsNoDedup reads lenHint
  result <- validateArraysIO tvars expected n
  return (result == 0)

-- | Validate the current transaction's read set before a potentially-divergent
-- continuation (C-2).  We validate the wait set, which is exactly the set of
-- live-memory reads.  'True' if still consistent.
validateTx :: TxState -> IO Bool
validateTx st = validateReads (txReads st) (txReadsLen st)

-----------------------------------------------------------------------------
-- Logged TVar access.
-----------------------------------------------------------------------------

-- | Read a 'TVar' through the log.  Consult writes first (read-your-own-write),
-- then reads (a consistent re-read), then live memory.  A hit on either log
-- records no new dependency — the dependency was captured when the write's or
-- read's @expected@ was first established.  Only a live-memory miss grows the
-- read set, keeping it exactly the set of live-memory reads (never write-only
-- TVars).
readTVarTx :: TxState -> TVar a -> IO (a, TxState)
readTVarTx st tv =
  case writeLookup tv (txWrites st) of
    Just (_, newVal) -> return (newVal, st)            -- read your own write
    Nothing ->
      case readLookup tv (txReads st) of
        Just expected -> return (expected, st)          -- consistent re-read
        Nothing -> do
          val <- readTVarIO tv
          let st' = st
                { txReads    = ReadEntry tv val : txReads st
                , txReadsLen = txReadsLen st + 1
                }
          return (val, st')

-- | Write a 'TVar' through the log.  The @expected@ value is the one this
-- transaction already associates with the 'TVar' — its earlier write's
-- @expected@, or the value it read — else a fresh live read on first touch.
-- Cons a fresh entry to the front (front-most wins at marshalling, so this is
-- last-write-wins without rewriting the spine).  Writes never touch the read
-- set (write-only TVars are not waited on).
writeTVarTx :: TxState -> TVar a -> a -> IO TxState
writeTVarTx st tv val = do
  expected <- case writeLookup tv (txWrites st) of
    Just (ex, _) -> return ex                           -- keep the original expected
    Nothing -> case readLookup tv (txReads st) of
      Just ex -> return ex                              -- expected = the value we read
      Nothing -> readTVarIO tv                          -- first touch: read live
  return st
    { txWrites    = WriteEntry tv expected val : txWrites st
    , txWritesLen = txWritesLen st + 1
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

-- | Batch-read a fragment's read set with 'readMany#', fold the snapshot into
-- 'txReads', then evaluate the fragment against the now-populated log (each
-- 'PRead' becomes a hit; writes proceed normally).  Returns 'Nothing' (caller
-- falls back to per-read evaluation) when the plan is not a fragment, has fewer
-- than two distinct reads (no batch payoff), or has a read already resolvable
-- from the log; otherwise 'Just' the evaluated fragment.
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
          -- 'readMany#' gives each TVar an individually-stable read but does not
          -- detect a cross-batch tear (a commit landing between two of the
          -- reads); it always reports 0.  Cross-batch inconsistency is caught
          -- downstream by 'validateTx' before the next 'SBind' and by the commit
          -- check, so we always fold the batch in.
          _ <- readManyArraysIO tvars results expected n
          st' <- foldReads st 0 n tvars results
          (out, st'') <- evalApp st' plan
          return (Just (out, st''))
    _ -> return Nothing

-- | Is a read of this 'TVar' resolvable from the current transaction state
-- without touching live memory — i.e. already written or read?  Such TVars must
-- be served by 'readTVarTx', never batched through 'readMany#' (which reads live
-- memory and would miss an earlier logged write).
readResolvable :: TVar a -> TxState -> Bool
readResolvable tv st =
  case writeLookup tv (txWrites st) of
    Just _ -> True
    Nothing -> case readLookup tv (txReads st) of
      Just _ -> True
      Nothing -> False

-- Fold a readMany# result batch into the read set.  Each TVar becomes a read
-- entry (skipping addresses already in the read set, preserving first-match
-- semantics).  'tryReadMany' has already bailed if any batch TVar was logged on
-- entry, so the only dedup needed here is intra-batch.
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
      case readLookup tv (txReads st) of
        Just _ -> foldReads st (i + 1) n tvars results
        Nothing -> do
          let val = coerceVal valAny
              st' = st
                { txReads    = ReadEntry tv val : txReads st
                , txReadsLen = txReadsLen st + 1
                }
          foldReads st' (i + 1) n tvars results

anyToTVar :: Any -> TVar a
anyToTVar a = TVar (unsafeCoerce# a)
{-# INLINE anyToTVar #-}

-- Note [Discard writes, keep reads]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'orElse' (when the left branch retries) and 'catchSTM' (when the body throws)
-- perform the *same* operation on the transaction state: discard the abandoned
-- sub-computation's writes, but keep its reads.  With the read/write split this
-- is two O(1) field updates — restore the entering 'txWrites', keep the (now
-- larger) 'txReads' — so both arms share one shape:
--
--     evalSTM (st { txReads = txReads sub, txReadsLen = txReadsLen sub }) k
--
-- where @st@ is the entering state (its 'txWrites' is the rollback target) and
-- @sub@ is the state after the abandoned branch\/body (its monotone 'txReads'
-- already carries the union of the entering reads and the sub-computation's
-- reads).  This mirrors legacy @merge_read_into@ (rts/STM.c): an aborted nested
-- transaction's read set is merged into its parent so the parent stays validated
-- and woken against the snapshot the retry\/throw was based on.
--
-- Legacy additionally re-records the *expected* value of each TVar the abandoned
-- branch *wrote* as a parent read.  We drop those, and the difference is not
-- observable: a discarded write can only influence the outcome through a value
-- that was read, and every such read is a genuine read entry that we keep.  A
-- write whose expected is never read back cannot change the result, so omitting
-- it changes nothing a caller can detect (it only avoids some spurious retries).

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
      Retry ->
        -- Discard the left branch's writes (restore the entering 'txWrites'),
        -- keep its reads (the monotone 'txReads' already carries the union), then
        -- run the right branch.  See Note [Discard writes, keep reads].
        evalSTM (st { txReads = txReads stL, txReadsLen = txReadsLen stL }) right
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
        -- A caught exception discards the body's writes (restore the entering
        -- 'txWrites') but keeps its reads, so the enclosing transaction stays
        -- validated/woken against the snapshot the throw was based on.  Same
        -- shape as the orElse-retry arm; see Note [Discard writes, keep reads].
        evalSTM (st { txReads = txReads stBody, txReadsLen = txReadsLen stBody })
                (handler e)
  SUnsafeIO io ->
    catchSTMIO
      (do
        a <- io
        return (Ok a, st))
      (\e -> return (Raise e, st))
  SFix k -> evalFix st k

-- One-TVar-at-a-time evaluation of an applicative fragment, via 'evalPrim'.
-- Used both as the 'readMany#' fall-back (reads go through 'readTVarTx') and to
-- re-evaluate a fragment after a successful batch (every 'PRead' is now a log
-- hit).  The 'SApp' arm recurses into 'evalApp', never 'evalSTM', so it does not
-- re-attempt 'readMany#' — that is what makes the post-batch re-evaluation
-- terminate.
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
          success <- commitTx (txWrites st) (txWritesLen st)
                              (txReads st) (txReadsLen st)
          if success
            then return a
            else go  -- commit conflict: stmCommitLog# already unlocked; restart
        Retry -> do
          -- C-2: re-validate the read set before committing to a block.  An
          -- invalidated/zombie transaction (some logged read has since changed)
          -- restarts immediately; only a genuinely-consistent retry blocks on
          -- the union of every branch's reads.
          consistent <- validateReads (txReads st) (txReadsLen st)
          if not consistent
            then go
            else do
              registerReads (txReads st) (txReadsLen st)
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
      success <- commitTx [WriteEntry tv expected val] 1 [] 0
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
