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
-- == The CPS STM, in brief
--
-- @STM a@ is a continuation-passing computation, not an interpreted AST: it is a
-- function that takes the entering transaction state plus three continuations —
-- success, @retry@, and @throw@ — and invokes exactly one of them with the
-- resulting state (see 'STM').  '>>=' and '<*>' are plain closure compositions
-- that thread the state and pass @retry@\/@throw@ through; 'orElse'\/'catchSTM'
-- install a replacement @retry@\/@throw@ continuation that restores the entering
-- writes and keeps the reads (O(1) rollback, no exceptions); 'unsafeIOToSTM'
-- runs its 'IO' and routes a thrown exception into the @throw@ continuation;
-- 'mfixSTM' ties the knot with explicit black-holing.  'atomically' runs the
-- computation against an /immutable/ transaction log with continuations that
-- commit, block, or rethrow against the RTS.
--
-- There is no per-step outcome box and no interpreted-node allocation: '>>='
-- allocates ~one closure, and the only other per-op boxing is the immutable
-- cons-front log entries themselves.
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
-- updates ('keepReads'), no diffing, no spine rebuild (see Note [Discard writes,
-- keep reads]).  It is also why registration happens exactly once at the top (no
-- mid-flight register\/clear churn, no @RetryWithWait@ outcome, no
-- @differenceTxLog@): the monotone read set already holds the union of every
-- branch's reads, so nothing registers until the whole transaction retries.
--
-- Both lists insert by /consing to the front/ (O(1), no spine rebuild) and look
-- up by /first match/; de-duplication is deferred to the single commit
-- marshalling pass (where writes shadow reads of the same 'TVar').  Lengths are
-- tracked incrementally so marshalling needs no separate @length@ traversal.
--
-- == Validation
--
-- Reads are taken from live memory at access time, so between two reads the
-- computation can be running arbitrary user code over a mutually-inconsistent
-- snapshot.  'validateTx' is a 'readTVarIO' pointer-equality walk over
-- 'txReads'.  It is always used at the top-level @retry@ boundary; the monadic
-- '>>=' uses 'validateForBind' to validate only reads added since the previous
-- advisory checkpoint.  A mid-flight mismatch abandons the current attempt as a
-- @retry@; 'atomically' re-validates the read set before blocking, so an
-- invalidated (\"zombie\") transaction restarts immediately instead of blocking,
-- while a genuine @retry@ blocks.  Commit-time validation in 'stmCommitLog#' is
-- the correctness backstop.  Not re-checking old reads at every advisory
-- checkpoint can delay zombie detection, but cannot let an inconsistent
-- transaction commit or block on the wrong wait set.
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
import GHC.Internal.Num
import GHC.Internal.Unsafe.Coerce (unsafeCoerce#)
-- Upstream's "Refine GHC.Internal.Base imports" (6f4f6cf03a) slimmed Base's
-- re-export of GHC.Internal.Prim, so import the primitive types/classes directly.
import GHC.Internal.Prim
import GHC.Internal.Types ( IO(..), Bool(..), Int(..), Any, isTrue# )
import GHC.Internal.Classes ( Eq(..), Ord(..), not )
import GHC.Internal.Maybe ( Maybe(..) )
-- Explicit black-holing for 'mfixSTM', reusing the fixIO/fixST shape.  These
-- modules sit below Conc.STM in the import graph (none depend on it), so there
-- is no cycle.  'catch'/'throwIO' also serve 'unsafeIOToSTM' (see 'tryIO').
import GHC.Internal.IO ( catch, throwIO )
import GHC.Internal.MVar ( newEmptyMVar, readMVar, putMVar )
import GHC.Internal.IO.Unsafe ( unsafeDupableInterleaveIO )
import GHC.Internal.IO.Exception ( FixIOException(..), BlockedIndefinitelyOnMVar(..) )

-----------------------------------------------------------------------------
-- Transactional heap operations
-----------------------------------------------------------------------------

-- TVars are shared memory locations which support atomic memory
-- transactions.

-- | The success continuation: a result @a@ with the (post-effect) state.
type OkK a r = TxState -> a -> IO r
-- | The @retry@ continuation: carries the state whose read set is the wait set.
type RetryK r = TxState -> IO r
-- | The @throw@ continuation: carries the state (its reads are merged by an
-- enclosing 'catchSTM') and the exception.
type RaiseK r = TxState -> SomeException -> IO r

-- | @STM a@ in continuation-passing style.  Given the entering transaction state
-- and three continuations — success ('OkK'), @retry@ ('RetryK'), and @throw@
-- ('RaiseK') — an @STM a@ threads the state through its effects and invokes
-- exactly one continuation.  There is no intermediate AST or per-step outcome
-- box: '>>='\/'<*>' are plain closure compositions, 'orElse'\/'catchSTM' install
-- a replacement @retry@\/@throw@ continuation (O(1) rollback, no exceptions), and
-- the immutable cons-front log ('TxState') is carried as the first argument.
newtype STM a = STM
  { runSTM :: forall r. TxState -> OkK a r -> RetryK r -> RaiseK r -> IO r }

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

-- | The transaction state threaded through the computation.  The log is split
-- by access kind into two immutable cons-front lists (see the module header),
-- each with an incrementally-tracked length so marshalling needs no @length@
-- pass.  The split is what makes 'orElse' and 'catchSTM' O(1): both keep the
-- monotone reads and restore only the writes.
data TxState = TxState
  { txReads     :: ReadSet   -- monotone reads = wait set = read-validation set;
                             -- never rolled back within an attempt
  , txReadsLen  :: !Int      -- length of txReads (upper bound; pre-dedup)
  , txCheckedReadsLen :: !Int
                             -- length at last successful advisory validation
  , txWrites    :: WriteSet  -- speculative writes; rolled back by orElse and catchSTM
  , txWritesLen :: !Int      -- length of txWrites (upper bound; pre-dedup)
  }

emptyTxState :: TxState
emptyTxState = TxState [] 0 0 [] 0

-- | Pointer identity of two 'TVar's, via the levity-polymorphic, hetero-typed
-- 'reallyUnsafePtrEquality#' directly on the boxed 'TVar#' — no 'Addr#'
-- reinterpretation.  This is the one identity primitive; 'tvarSeen' and the
-- 'Eq' instance both go through it.
sameTVar :: TVar a -> TVar b -> Bool
sameTVar (TVar tv1#) (TVar tv2#) = isTrue# (reallyUnsafePtrEquality# tv1# tv2#)

-- | Coerce a logged value back to the accessor's type.  Sound by the
-- per-transaction fixed-type invariant documented on the entry types: every
-- entry for a given 'TVar' was written\/read at the one type the 'TVar' holds.
-- This is the single value-coercion primitive; 'writeLookup' and 'readLookup'
-- both route through it.
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

-- | Validate the read set: 'True' if every logged read is still pointer-equal to
-- its 'TVar''s current value.  Walks the read set directly with 'readTVarIO' +
-- 'reallyUnsafePtrEquality#' — NO array marshalling, so it allocates nothing.
-- The old path re-marshalled the whole (growing) read set into fresh arrays for
-- 'validate#' on /every/ bind (C-2), which is O(n²) allocation over a large
-- transaction; this is the single biggest allocation sink for long monadic txns.
--
-- Correctness vs the old lock-free 'validate#': 'readTVarIO#' spins past a commit
-- lock ('TREC_HEADER') and returns the committed value, so we wait out any
-- in-flight committer and then compare, needing no @num_updates@ recheck (that
-- recheck only existed because 'validate#' raced committers instead of waiting).
-- A write installs a fresh value pointer, so pointer-inequality ⇔ the read went
-- stale — exactly the test 'validate#' performed.  Mid-flight this is the
-- advisory zombie check; the lock-taking commit path remains authoritative.  The
-- trade-off is that a contended validation spin-waits rather than restarting
-- optimistically, which only matters for tiny heavily-contended transactions
-- (1–2 reads), where validation is trivial either way.
validateReads :: ReadSet -> IO Bool
validateReads = go
  where
    go [] = return True
    go (entry : rest) = do
      consistent <- validateReadEntry entry
      if consistent
        then go rest
        else return False

-- | Validate the newest @n@ reads in a read set.  Since 'txReads' is cons-front
-- and 'txCheckedReadsLen' records the length at the last advisory checkpoint,
-- this is exactly the set of reads added since then.
validateReadsPrefix :: Int -> ReadSet -> IO Bool
validateReadsPrefix = go
  where
    go n _
      | n <= 0 = return True
    go _ [] = return True
    go n (entry : rest) = do
      consistent <- validateReadEntry entry
      if consistent
        then go (n - 1) rest
        else return False

validateReadEntry :: ReadEntry -> IO Bool
validateReadEntry (ReadEntry tv expected) = do
  cur <- readTVarIO tv
  return (isTrue# (reallyUnsafePtrEquality# cur expected))

-- | Validate the entire current transaction's read set.  Used before committing
-- to a block in 'atomically'; 'validateForBind' handles advisory mid-flight
-- checkpoints.  'True' if still consistent.
validateTx :: TxState -> IO Bool
validateTx st = validateReads (txReads st)

-- | Advisory mid-flight validation before a monadic '>>=' continuation.  Only
-- reads added since the previous checkpoint are checked here.  Older reads are
-- still validated before blocking and by 'stmCommitLog#' under lock before any
-- successful commit.  Skipping their repeated mid-flight checks weakens only
-- early zombie detection: code may run longer on an obsolete snapshot, but it
-- cannot successfully commit or block until the full read set is checked.
validateForBind :: TxState -> IO (Bool, TxState)
validateForBind st =
  let unchecked = txReadsLen st - txCheckedReadsLen st in
  if unchecked <= 0
    then return (True, st)
    else do
      consistent <- validateReadsPrefix unchecked (txReads st)
      if consistent
        then return (True, st { txCheckedReadsLen = txReadsLen st })
        else return (False, st)

-----------------------------------------------------------------------------
-- Logged TVar access.
-----------------------------------------------------------------------------

-- | Cons a read onto the monotone read set, bumping its tracked length.  The
-- single place 'txReads' grows.
logRead :: TVar a -> a -> TxState -> TxState
logRead tv val st = st
  { txReads    = ReadEntry tv val : txReads st
  , txReadsLen = txReadsLen st + 1
  }

-- | Cons a write onto the write set, bumping its tracked length.  The single
-- place 'txWrites' grows.
logWrite :: TVar a -> a -> a -> TxState -> TxState
logWrite tv expected val st = st
  { txWrites    = WriteEntry tv expected val : txWrites st
  , txWritesLen = txWritesLen st + 1
  }

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
          return (val, logRead tv val st)

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
  return (logWrite tv expected val st)

-- | Restore @entering@'s speculative writes while keeping @sub@'s monotone
-- reads.  The single rollback operation shared by 'orElse' (left retried) and
-- 'catchSTM' (body threw); see Note [Discard writes, keep reads].
keepReads :: TxState -> TxState -> TxState
keepReads entering sub = entering
  { txReads = txReads sub
  , txReadsLen = txReadsLen sub
  , txCheckedReadsLen = txCheckedReadsLen sub
  }
{-# INLINE keepReads #-}

-- Note [Discard writes, keep reads]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'orElse' (when the left branch retries) and 'catchSTM' (when the body throws)
-- perform the *same* operation on the transaction state: discard the abandoned
-- sub-computation's writes, but keep its reads.  With the read/write split this
-- is two O(1) field updates — restore the entering 'txWrites', keep the (now
-- larger) 'txReads' — captured once in 'keepReads':
--
--     keepReads entering sub
--
-- where @entering@ is the state on entry (its 'txWrites' is the rollback target)
-- and @sub@ is the state the abandoned branch\/body invoked its retry\/raise
-- continuation with (its monotone 'txReads' already carries the union of the
-- entering reads and the sub-computation's reads).  This mirrors legacy
-- @merge_read_into@ (rts/STM.c): an aborted nested transaction's read set is
-- merged into its parent so the parent stays validated and woken against the
-- snapshot the retry\/throw was based on.
--
-- Legacy additionally re-records the *expected* value of each TVar the abandoned
-- branch *wrote* as a parent read.  We drop those, and the difference is not
-- observable: a discarded write can only influence the outcome through a value
-- that was read, and every such read is a genuine read entry that we keep.  A
-- write whose expected is never read back cannot change the result, so omitting
-- it changes nothing a caller can detect (it only avoids some spurious retries).

-- Note [Which TxState flows to each continuation]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Every combinator invokes one of three continuations with a 'TxState'.  The
-- state carried is the POST-effect state (its 'txReads' is consumed even on the
-- non-success continuations), so combinators thread the accumulated state, not
-- the entering one:
--
--   * ok    — full state to commit: 'txWrites' applied, 'txReads' validated.
--   * retry — 'txReads' is the wait set.  An enclosing 'orElse' carries it into
--             the sibling branch; at the top level 'atomically' registers it.
--             'txWrites' is irrelevant (rolled back / unused).
--   * raise — 'txReads' is merged by an enclosing 'catchSTM' (the body's reads
--             keep the handler validated against the throw's snapshot); at the
--             top level it is discarded by 'raiseIOIO'.  'txWrites' is discarded.
--
-- 'orElse'\/'catchSTM' install a replacement retry\/raise continuation that
-- 'keepReads' (restore entering writes, keep the abandoned branch's reads)
-- before running the sibling\/handler.  'mfixSTM' passes the body's accumulated
-- state through on /every/ continuation, so a @mfix@ body that reads TVars and
-- then retries\/throws surfaces those reads to the enclosing 'orElse'\/'catchSTM'.

-----------------------------------------------------------------------------
-- Instances.
-----------------------------------------------------------------------------

instance Functor STM where
  fmap f (STM m) = STM $ \st ok retryK raise ->
    m st (\st' a -> ok st' (f a)) retryK raise
  {-# INLINE fmap #-}

-- | @since base-4.8.0.0
instance Applicative STM where
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}
  {-# INLINE liftA2 #-}
  {-# INLINE (*>) #-}
  {-# INLINE (<*) #-}
  pure x = STM $ \st ok _ _ -> ok st x
  -- Run both effects in sequence with no spine: this is what makes
  -- 'traverse'\/'mapM'\/'sequenceA' over 'readTVar' O(n) instead of O(n²).
  STM mf <*> STM mx = STM $ \st ok retryK raise ->
    mf st (\st' f -> mx st' (\st'' x -> ok st'' (f x)) retryK raise) retryK raise
  liftA2 f (STM mx) (STM my) = STM $ \st ok retryK raise ->
    mx st (\st' x -> my st' (\st'' y -> ok st'' (f x y)) retryK raise) retryK raise
  STM ma *> STM mb = STM $ \st ok retryK raise ->
    ma st (\st' _ -> mb st' ok retryK raise) retryK raise
  STM ma <* STM mb = STM $ \st ok retryK raise ->
    ma st (\st' a -> mb st' (\st'' _ -> ok st'' a) retryK raise) retryK raise

-- | @since base-4.3.0.0
instance  Monad STM  where
    {-# INLINE (>>=) #-}
    -- After the left side succeeds, validate the reads added since the previous
    -- checkpoint (C-2) before running the arbitrary, possibly-divergent
    -- continuation.  A stale snapshot abandons the attempt via the @retry@
    -- continuation; 'atomically' re-validates and restarts immediately.
    STM m >>= k = STM $ \st ok retryK raise ->
      m st
        (\st' a -> do
            (consistent, st'') <- validateForBind st'
            if consistent
              then runSTM (k a) st'' ok retryK raise
              else retryK st'')
        retryK raise
    (>>) = (*>)

-- | @since base-4.17.0.0
instance Semigroup a => Semigroup (STM a) where
    (<>) = liftA2 (<>)

-- | @since base-4.17.0.0
instance Monoid a => Monoid (STM a) where
    mempty = pure mempty

-- | @mfix@ for STM.  Ties the knot inside the transaction, matching the legacy
-- @MonadFix STM@ semantics, but with /explicit/ black-holing (an MVar-free
-- analogue is impossible here, so we reuse the 'fixIO'\/'fixST' shape) rather
-- than the lazy @State#@ knot the old instance used.  The lazy knot is exactly
-- what @fixST@ abandoned in #15349: lazy black-holing can /re-run/ the
-- effectful body and duplicate its reads\/writes.  Here the body is run exactly
-- once; the fixed-point value is forced lazily and, if demanded before the body
-- yields success, diverges into the black hole (raising 'FixIOException'),
-- preserving the legacy \"forcing diverges\" contract for @retry@\/@throw@
-- outcomes.  See "GHC.Internal.Control.Monad.ST.Imp".
mfixSTM :: (a -> STM a) -> STM a
mfixSTM k = STM $ \st ok retryK raise -> do
  m <- newEmptyMVar
  ans <- unsafeDupableInterleaveIO
           (readMVar m `catch` \BlockedIndefinitelyOnMVar -> throwIO FixIOException)
  runSTM (k ans) st
    -- success: publish the fixed point, then continue.
    (\st' a -> do putMVar m a; ok st' a)
    -- retry/raise: leave m empty, so forcing `ans` blocks indefinitely; the
    -- runtime detects the deadlock (BlockedIndefinitelyOnMVar) and we re-raise
    -- it as the standard 'FixIOException'.  Matches the legacy 'mfix' contract
    -- without the lazy-State#-knot re-run hazard of #15349.
    retryK
    raise
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
unsafeIOToSTM io = STM $ \st ok _ raise -> do
  -- Run only the embedded IO under 'catch'; build (but do not run) the chosen
  -- continuation, then run it OUTSIDE the catch so the rest of the transaction
  -- is not swallowed by this handler.  Only the action's own exceptions are
  -- caught (its result is not forced), matching the legacy behaviour.
  next <- catch (do a <- io
                    return (ok st a))
                (\e -> return (raise st e))
  next

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
atomically (STM m) = atomicallyIO (runAtomicallyCPS m)

-- | Drive a CPS transaction against the RTS: run it from an empty log with
-- continuations that commit (on success), validate-and-block or restart (on
-- @retry@), or rethrow (on @throw@).  @go@ is the restart loop, shared by a
-- commit conflict and a zombie @retry@.  There is no per-attempt outcome box:
-- the continuations drive the RTS directly and recurse into @go@ to restart.
runAtomicallyCPS
  :: (forall r. TxState -> OkK a r -> RetryK r -> RaiseK r -> IO r) -> IO a
runAtomicallyCPS m = go
  where
    go = m emptyTxState onOk onRetry onRaise
    onOk st a = do
      success <- commitTx (txWrites st) (txWritesLen st)
                          (txReads st) (txReadsLen st)
      if success
        then return a
        else go  -- commit conflict: stmCommitLog# already unlocked; restart
    onRetry st = do
      -- C-2: re-validate the read set before committing to a block.  An
      -- invalidated/zombie transaction (some logged read has since changed)
      -- restarts immediately; only a genuinely-consistent retry blocks on the
      -- union of every branch's reads.
      consistent <- validateTx st
      if not consistent
        then go
        else do
          registerReads (txReads st) (txReadsLen st)
          blockOnRegisteredIO
          go
    onRaise _ e = raiseIOIO e

-- | Retry execution of the current memory transaction because it has seen
-- values in 'TVar's which mean that it should not continue (e.g. the 'TVar's
-- represent a shared buffer that is now empty).  The implementation may
-- block the thread until one of the 'TVar's that it has read from has been
-- updated. (GHC only)
retry :: STM a
retry = STM $ \st _ retryK _ -> retryK st

-- | Compose two alternative STM actions (GHC only).
--
-- If the first action completes without retrying then it forms the result of
-- the 'orElse'. Otherwise, if the first action retries, then the second action
-- is tried in its place. If both actions retry then the 'orElse' as a whole
-- retries.
orElse :: STM a -> STM a -> STM a
orElse (STM ma) (STM mb) = STM $ \st ok retryK raise ->
  -- Success/throw of the left branch pass straight through (carrying the left's
  -- accumulated state).  A left @retry@ runs the right branch with the left's
  -- writes discarded and reads kept; see Note [Discard writes, keep reads].
  ma st ok (\stL -> mb (keepReads st stL) ok retryK raise) raise

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
  in STM $ \st _ _ raise -> raise st ex

-- | Exception handling within STM actions.
--
-- @'catchSTM' m f@ catches any exception thrown by @m@ using 'throwSTM',
-- using the function @f@ to handle the exception. If an exception is
-- thrown, any changes made by @m@ are rolled back, but changes prior to
-- @m@ persist.
catchSTM :: Exception e => STM a -> (e -> STM a) -> STM a
catchSTM (STM body) handler = STM $ \st ok retryK raise ->
  -- Success and @retry@ of the body pass through (a retry is not caught; the
  -- body's reads stay in the wait set).  On @throw@, if the exception matches
  -- the handler's type, run the handler with the body's writes discarded and
  -- reads kept; otherwise rethrow.  See Note [Discard writes, keep reads].
  body st ok retryK
    (\stBody e -> case fromException e of
        Just e' -> runSTM (handler e') (keepReads st stBody) ok retryK raise
        Nothing -> raise stBody e)

-- |Shared memory locations that support atomic memory transactions.
data TVar a = TVar (TVar# RealWorld a)

-- | @since base-4.8.0.0
instance Eq (TVar a) where
        (==) = sameTVar

-- | Create a new 'TVar' holding a value supplied
newTVar :: a -> STM (TVar a)
newTVar val = STM $ \st ok _ _ -> do
  tv <- newTVarIO val
  ok st tv

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
readTVar tv = STM $ \st ok _ _ -> do
  (a, st') <- readTVarTx st tv
  ok st' a

-- |Write the supplied value into a 'TVar'.
writeTVar :: TVar a -> a -> STM ()
writeTVar tv val = STM $ \st ok _ _ -> do
  st' <- writeTVarTx st tv val
  ok st' ()
