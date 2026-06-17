{-# LANGUAGE ScopedTypeVariables #-}

-- #10 (regression #3b): a `catchSTM` body that reads a TVar and then throws must
-- retain that read in the enclosing transaction's wait set.  Legacy STM merges a
-- caught (aborted) nested transaction's read set into its parent
-- (`merge_read_into`, rts/STM.c), so an exception decision based on a TVar read
-- keeps the transaction waiting on that TVar.  An earlier version of the
-- plan-based interpreter rolled the wait set all the way back to the entering
-- state on a caught exception, dropping the body's reads — so a `retry` in the
-- handler would block on nothing the writer ever touched and never wake (a lost
-- wakeup).  Every wake here is guarded by a timeout so the regression fails
-- deterministically rather than hanging the suite.
module Main (main) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception (SomeException)
import Control.Monad
import System.Timeout
import System.Exit (exitFailure)
import GHC.Conc (unsafeIOToSTM)

timeoutUs :: Int
timeoutUs = 5 * 1000000

-- | Fork a transaction that first signals (via @ready@) that it has reached its
-- retry point, wait for that signal, then run @poke@ (which should wake it), and
-- finally require the transaction to complete within the timeout.
runWakeCase :: String -> ((() -> STM ()) -> STM a) -> IO () -> (a -> IO ()) -> IO ()
runWakeCase name mkTxn poke checkResult = do
  ready <- newEmptyMVar
  done  <- newEmptyMVar
  let signal _ = unsafeIOToSTM (void (tryPutMVar ready ()))
  _ <- forkIO $ do
        r <- atomically (mkTxn signal)
        putMVar done r
  reached <- timeout timeoutUs (takeMVar ready)
  case reached of
    Nothing -> die (name ++ ": transaction never reached its retry point")
    Just () -> return ()
  poke
  m <- timeout timeoutUs (takeMVar done)
  case m of
    Nothing -> die (name ++ ": LOST WAKEUP - transaction did not wake")
    Just r  -> checkResult r
  where
    die msg = putStrLn msg >> exitFailure

main :: IO ()
main = do
  -- Case 1: the core regression.  The body reads `x`; while `x` is False it
  -- signals and throws, the handler retries, and the whole transaction blocks.
  -- The only TVar that can wake it is `x` (read inside the body before the
  -- throw).  If the caught body's read is dropped from the wait set, the write
  -- to `x` never wakes the transaction and the timeout fires.
  do
    x <- newTVarIO False
    let mk signal = catchSTM
          (do v <- readTVar x
              if v
                then return "committed"
                else do signal ()
                        throwSTM (userError "boom"))
          (\(_ :: SomeException) -> retry)
    runWakeCase "catch-body-read"
      mk
      (atomically (writeTVar x True))
      (\r -> when (r /= "committed")
               (putStrLn ("catch-body-read: unexpected result " ++ show r) >> exitFailure))

  -- Case 2: the caught body's read must survive an enclosing `orElse`.  The
  -- catch sits in the left branch; when its handler retries, the left branch
  -- retries and `orElse` falls through to the right branch (which reads `y` and
  -- retries), so the transaction blocks on the union { x, y }.  We poke ONLY
  -- `x` — the TVar read inside the caught body.  If `demoteReads`' retained read
  -- did not survive the `orElse` wait-set carry-forward, this never wakes.
  do
    x <- newTVarIO False
    y <- newTVarIO False
    let mk signal =
          let left = catchSTM
                (do v <- readTVar x
                    if v
                      then return "committed"
                      else do signal ()
                              throwSTM (userError "boom"))
                (\(_ :: SomeException) -> retry)
              right = do
                _ <- readTVar y
                retry
          in left `orElse` right
    runWakeCase "catch-body-read-orElse"
      mk
      (atomically (writeTVar x True))
      (\r -> when (r /= "committed")
               (putStrLn ("catch-body-read-orElse: unexpected result " ++ show r) >> exitFailure))

  -- Case 3 (regression guard): an ordinary caught exception whose handler
  -- returns normally must still commit, and the body's discarded write must not
  -- leak — the handler observes the pre-body value.
  do
    x <- newTVarIO (0 :: Int)
    r <- atomically $
           catchSTM
             (do writeTVar x 99                       -- discarded write
                 throwSTM (userError "boom"))
             (\(_ :: SomeException) -> readTVar x)     -- must observe 0
    when (r /= 0)
      (putStrLn ("catch-handler-commit: body write leaked, saw " ++ show r) >> exitFailure)

  putStrLn "stm_catch_wait: all catchSTM wait-set cases woke"
