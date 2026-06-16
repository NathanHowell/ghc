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
import GHC.Internal.List (length)
import GHC.Internal.Num
import GHC.Internal.Unsafe.Coerce (unsafeCoerce#)

-----------------------------------------------------------------------------
-- Transactional heap operations
-----------------------------------------------------------------------------

-- TVars are shared memory locations which support atomic memory
-- transactions.

-- |A monad supporting atomic memory transactions.
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

data TxEntry where
  TxEntry :: TVar a -> a -> a -> TxEntry

-- Entries are (tvar, expected, new).
type TxLog = [TxEntry]

data STMOutcome a = Ok a | Retry | RetryWithWait | Raise SomeException

data STMResult a = STMResult (State# RealWorld) (STMOutcome a) TxLog

-- Placeholder used to initialize arrays before they are filled; value is never read.
emptyAny :: Any
emptyAny = unsafeCoerce# (0# :: Int#)

emptyTxLog :: TxLog
emptyTxLog = []

sameTVar :: TVar a -> TVar b -> Bool
sameTVar (TVar tv1#) (TVar tv2#) =
  isTrue# (eqAddr# (unsafeCoerce# tv1#) (unsafeCoerce# tv2#))

-- Like Prelude.lookup, but specialized for the TxLog association list.
lookupTxLog :: TVar a -> TxLog -> Maybe (a, a)
lookupTxLog _ [] = Nothing
lookupTxLog tv (TxEntry tv' expected newVal:rest)
  | sameTVar tv tv' = Just (unsafeCoerce# expected, unsafeCoerce# newVal)
  | otherwise = lookupTxLog tv rest

-- Like insert/replace into an association list (keeps at most one entry).
insertTxLog :: TVar a -> a -> a -> TxLog -> TxLog
insertTxLog tv expected newVal [] = [TxEntry tv expected newVal]
insertTxLog tv expected newVal (entry@(TxEntry tv' _ _):rest)
  | sameTVar tv tv' = TxEntry tv expected newVal : rest
  | otherwise = entry : insertTxLog tv expected newVal rest

-- Like list difference based on tvars: left entries whose tvars are absent in right.
-- O(n*m) scan is acceptable for typical small transactions.
differenceTxLog :: TxLog -> TxLog -> TxLog
differenceTxLog [] _ = []
differenceTxLog (entry@(TxEntry tv _ _):rest) log =
  case tvarInLog tv log of
    True -> differenceTxLog rest log
    False -> entry : differenceTxLog rest log

tvarInLog :: TVar a -> TxLog -> Bool
tvarInLog _ [] = False
tvarInLog tv (TxEntry tv' _ _ : rest)
  | sameTVar tv tv' = True
  | otherwise = tvarInLog tv rest

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

clearRegistrationsIO :: IO ()
clearRegistrationsIO = stateToIO_ clearRegistrations#
{-# INLINE clearRegistrationsIO #-}

newSmallArrayIO :: Int -> Any -> IO (SmallMutableArray# RealWorld Any)
newSmallArrayIO (I# n#) initVal = IO $ \s0 ->
  case newSmallArray# n# initVal s0 of
    (# s1, arr #) -> (# s1, arr #)

writeSmallArrayIO :: SmallMutableArray# RealWorld Any -> Int -> Any -> IO ()
writeSmallArrayIO arr (I# i#) val = stateToIO_ (writeSmallArray# arr i# val)

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

registerRetriesLog :: TxLog -> IO ()
registerRetriesLog [] = return ()
registerRetriesLog log = do
  let n = length log
  tvars <- newSmallArrayIO n emptyAny
  expected <- newSmallArrayIO n emptyAny
  let go _ [] = return ()
      go i (TxEntry (TVar tv#) expectedVal _ : rest) = do
        writeSmallArrayIO tvars i (unsafeCoerce# tv#)
        writeSmallArrayIO expected i (unsafeCoerce# expectedVal)
        go (i + 1) rest
  go 0 log
  registerLogRangeArraysIO tvars expected 0 n

commitTxLog :: TxLog -> IO Bool
commitTxLog [] = return True
commitTxLog log = do
  let n = length log
  tvars <- newSmallArrayIO n emptyAny
  expected <- newSmallArrayIO n emptyAny
  new <- newSmallArrayIO n emptyAny
  let go _ [] = return ()
      go i (TxEntry (TVar tv#) expectedVal newVal : rest) = do
        writeSmallArrayIO tvars i (unsafeCoerce# tv#)
        writeSmallArrayIO expected i (unsafeCoerce# expectedVal)
        writeSmallArrayIO new i (unsafeCoerce# newVal)
        go (i + 1) rest
  go 0 log
  result <- stmCommitLogArraysIO tvars expected new n
  return (result == 0)

readTVarTx :: TxLog -> TVar a -> IO (a, TxLog)
readTVarTx log tv =
  case lookupTxLog tv log of
    Just (_, newVal) ->
      return (newVal, log)
    Nothing -> do
      val <- readTVarIO tv
      let log' = insertTxLog tv val val log
      return (val, log')

writeTVarTx :: TxLog -> TVar a -> a -> IO TxLog
writeTVarTx log tv val =
  case lookupTxLog tv log of
    Just (expected, _) ->
      return (insertTxLog tv expected val log)
    Nothing -> do
      expected <- readTVarIO tv
      let log' = insertTxLog tv expected val log
      return log'

evalPrim :: TxLog -> STMPrim a -> IO (a, TxLog)
evalPrim log prim = case prim of
  PRead tv -> readTVarTx log tv
  PWrite tv val -> do
    log' <- writeTVarTx log tv val
    return ((), log')
  PNewTVar val -> do
    tv <- newTVarIO val
    return (tv, log)

runRightAlternative :: TxLog -> STMPlan a -> IO (STMOutcome a, TxLog)
runRightAlternative log right = do
  (outcomeR, logR) <- evalSTM log right
  case outcomeR of
    Ok a -> do
      clearRegistrationsIO
      return (Ok a, logR)
    Raise e -> do
      clearRegistrationsIO
      return (Raise e, logR)
    Retry -> do
      registerRetriesLog logR
      return (RetryWithWait, logR)
    RetryWithWait -> do
      registerRetriesLog logR
      return (RetryWithWait, logR)

evalSTM :: TxLog -> STMPlan a -> IO (STMOutcome a, TxLog)
evalSTM log plan = case plan of
  SPure a -> return (Ok a, log)
  SPrim p -> do
    (a, log') <- evalPrim log p
    return (Ok a, log')
  SApp pf px -> do
    (outcome, log') <- evalSTM log pf
    case outcome of
      Ok f -> do
        (x, log'') <- evalPrim log' px
        return (Ok (f x), log'')
      Retry -> return (Retry, log')
      RetryWithWait -> return (RetryWithWait, log')
      Raise e -> return (Raise e, log')
  SBind p k -> do
    (outcome, log') <- evalSTM log p
    case outcome of
      Ok a -> evalSTM log' (k a)
      Retry -> return (Retry, log')
      RetryWithWait -> return (RetryWithWait, log')
      Raise e -> return (Raise e, log')
  SRetry ->
    return (Retry, log)
  SOrElse left right -> do
    (outcomeL, logL) <- evalSTM log left
    case outcomeL of
      Ok a ->
        return (Ok a, logL)
      Raise e ->
        return (Raise e, logL)
      Retry -> do
        registerRetriesLog (differenceTxLog logL log)
        runRightAlternative log right
      RetryWithWait -> do
        runRightAlternative log right
  SThrow e ->
    return (Raise e, log)
  SCatch body handler -> do
    (outcome, logBody) <- evalSTM log body
    case outcome of
      Ok a -> return (Ok a, logBody)
      Retry -> return (Retry, logBody)
      RetryWithWait -> return (RetryWithWait, logBody)
      Raise e -> do
        clearRegistrationsIO
        evalSTM log (handler e)
  SUnsafeIO io ->
    catchSTMIO
      (do
        a <- io
        return (Ok a, log))
      (\e -> return (Raise e, log))
  SFix k ->
    stateToIO $ \s0 ->
      let ans = case evalSTM log (k r) of
            IO m ->
              case m s0 of
                (# s1, (out, log') #) -> STMResult s1 out log'
          -- If the body doesn't yield Ok, forcing the fixed point should diverge.
          r = case ans of
            STMResult _ out _ -> case out of
              Ok a -> a
              _ -> errorWithoutStackTrace "mfix STM: diverging"
      in case ans of
           STMResult s1 out log' -> (# s1, (out, log') #)

runAtomically :: STMPlan a -> IO a
runAtomically plan = go emptyTxLog
  where
    go log = do
      clearRegistrationsIO
      (outcome, log') <- evalSTM log plan
      case outcome of
        Ok a -> do
          success <- commitTxLog log'
          if success
            then return a
            else go emptyTxLog
        Retry -> do
          registerRetriesLog log'
          blockOnRegisteredIO
          go emptyTxLog
        RetryWithWait -> do
          blockOnRegisteredIO
          go emptyTxLog
        Raise e -> do
          clearRegistrationsIO
          raiseIOIO e

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

    fastPrim f prim = case prim of
      PRead (TVar tvar#) ->
        Just (do
          a <- readTVarIO (TVar tvar#)
          return (f a))
      PNewTVar val ->
        Just (do
          tvar <- newTVarIO val
          return (f tvar))
      _ -> Nothing

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
