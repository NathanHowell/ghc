-- H-8: the important orElse property is that a blocked transaction waits on the
-- *union* of every branch's read set, including TVars read *before* the orElse.
-- The original test only ever wrote the right-branch TVar, so an incomplete
-- wait-set union (the C-3 lost-wakeup) would still pass.  Here we drive each of
-- the three failure modes independently, every wake guarded by a timeout so a
-- lost wakeup fails deterministically rather than hanging the suite.
module Main (main) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import System.Timeout
import System.Exit (exitFailure)
import GHC.Conc (unsafeIOToSTM)

timeoutUs :: Int
timeoutUs = 5 * 1000000

-- | Fork a transaction that first signals (via @ready@) that it has reached its
-- retry point, wait for that signal, then run @poke@ (which should wake it), and
-- finally require the transaction to complete within the timeout.  Returns the
-- transaction's result, or reports a lost wakeup.
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
  -- Case 1 (C-3 mode A): wake when ONLY the LEFT-branch TVar is written.
  -- left reads `a` and retries; right reads `b` and retries.  We write only `a`.
  -- A wait set that dropped the left branch's reads would never wake here.
  do
    a <- newTVarIO False
    b <- newTVarIO False
    let mk signal = do
          let left = do
                v <- readTVar a
                if v then return "left" else retry
              right = do
                _ <- readTVar b
                signal ()
                retry
          left `orElse` right
    runWakeCase "left-only"
      mk
      (atomically (writeTVar a True))
      (\r -> when (r /= "left") (putStrLn ("left-only: unexpected result " ++ show r) >> exitFailure))

  -- Case 2 (C-3 mode B): wake when ONLY a TVar read BEFORE the orElse is written.
  -- `pre` is read before the orElse and gates the whole transaction; both
  -- branches read their own (always-False) TVars and retry, so on the first pass
  -- the transaction blocks on the union { pre, a, b }.  We write ONLY `pre`, to a
  -- value that lets the transaction commit on re-run.  If the pre-orElse read is
  -- dropped from the wait set (exactly the C-3 SCatch/clear failure), this never
  -- wakes.  The signal fires only on the first (pre==0) pass so the wake is
  -- attributable to the `pre` write and not to spurious re-runs.
  do
    pre <- newTVarIO (0 :: Int)
    a   <- newTVarIO False
    b   <- newTVarIO False
    let mk signal = do
          p <- readTVar pre              -- read BEFORE the orElse
          if p /= 0
            then return "pre"            -- woken by the `pre` write: commit
            else do
              let left = do
                    v <- readTVar a
                    if v then return "left" else retry
                  right = do
                    _ <- readTVar b
                    signal ()
                    retry
              left `orElse` right
    runWakeCase "pre-orElse-only"
      mk
      (atomically (writeTVar pre 1))
      (\r -> when (r /= "pre")
               (putStrLn ("pre-orElse-only: unexpected result " ++ show r) >> exitFailure))

  -- Case 3 (regression guard): the original property - wake when ONLY the
  -- RIGHT-branch TVar is written - must still hold.
  do
    a <- newTVarIO False
    b <- newTVarIO False
    let mk signal = do
          let left = do
                v <- readTVar a
                if v then return "left" else retry
              right = do
                v <- readTVar b
                if v then return "right" else do
                  signal ()
                  retry
          left `orElse` right
    runWakeCase "right-only"
      mk
      (atomically (writeTVar b True))
      (\r -> when (r /= "right") (putStrLn ("right-only: unexpected result " ++ show r) >> exitFailure))

  putStrLn "stm_orElse_wait_union: all wait-set-union cases woke"
