{-# LANGUAGE ScopedTypeVariables #-}
-- Coverage for the new applicative-fragment machinery:
--   * validate#  - the C-2 zombie-abort path: a transaction that has read a
--     mutually-inconsistent snapshot must be aborted/restarted before running
--     arbitrary continuation code, not loop forever over the stale snapshot.
--   * readMany#  - batched read of an applicative fragment with >= 2 distinct
--     reads.  The batch must observe a *consistent* snapshot of all TVars.
module Main (main) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.IORef
import System.Exit (exitFailure)
import System.Timeout
import GHC.Conc (unsafeIOToSTM)

timeoutUs :: Int
timeoutUs = 5 * 1000000

bail :: String -> IO ()
bail msg = putStrLn msg >> exitFailure

main :: IO ()
main = do
  test_validate_zombie_abort
  test_readMany_consistent_snapshot
  putStrLn "stm_validate_readMany: ok"

-- validate#: the classic zombie.  The invariant a == b holds for every committed
-- state (a writer always updates both together).  A transaction reads a, then b;
-- if it ever observes a /= b it has a torn snapshot and must NOT proceed into the
-- divergent continuation - the read-set validation must abort and restart it.
-- We force a tear with a concurrent writer gated through unsafeIOToSTM, then loop
-- forever iff the snapshot is torn.  A correct validate# restarts the txn onto a
-- consistent snapshot, so it terminates (within the timeout) and never loops.
test_validate_zombie_abort :: IO ()
test_validate_zombie_abort = do
  a <- newTVarIO (0 :: Int)
  b <- newTVarIO (0 :: Int)
  ready <- newEmptyMVar       -- txn -> writer: "I have read a"
  done  <- newEmptyMVar       -- writer -> txn: "I have committed a/=b then a==b"
  gate  <- newIORef True      -- tear only on the first attempt
  let txn = do
        x <- readTVar a
        -- After reading `a`, hand off to the writer so it can commit a tearing
        -- update (a := 1) and then a reconciling update (b := 1) before we read
        -- b.  Only on the first attempt.
        first <- unsafeIOToSTM $ do
          g <- readIORef gate
          when g $ do
            writeIORef gate False
            putMVar ready ()
            takeMVar done
          return g
        y <- readTVar b
        -- If validate# fails to abort a torn read, x==0 and y==1 here and we
        -- diverge.  A correct implementation restarts before this point.
        when (first && x /= y) $
          let spin :: Int -> Int
              spin n = spin (n + 1)
          in unsafeIOToSTM (evaluate (spin 0)) >> return ()
        return (x, y)
  writer <- forkIO $ do
    takeMVar ready
    atomically (writeTVar a 1)   -- tear: now a=1, b=0
    atomically (writeTVar b 1)   -- reconcile: a=1, b=1
    putMVar done ()
  res <- timeout timeoutUs (atomically txn)
  killThread writer
  case res of
    Nothing       -> bail "validate-zombie: diverged on a torn snapshot (validate# did not abort)"
    Just (x, y)
      | x == y    -> return ()
      | otherwise -> bail ("validate-zombie: committed a torn snapshot " ++ show (x, y))

-- readMany#: an applicative fragment with several distinct reads is batched.
-- Against a writer that keeps the four TVars mutually equal, every committed
-- read batch must be internally consistent (all four equal) - the batch reads a
-- single consistent snapshot, never a tear across the fragment.
test_readMany_consistent_snapshot :: IO ()
test_readMany_consistent_snapshot = do
  t1 <- newTVarIO (0 :: Int)
  t2 <- newTVarIO (0 :: Int)
  t3 <- newTVarIO (0 :: Int)
  t4 <- newTVarIO (0 :: Int)
  stop <- newIORef False
  -- Writer bumps all four together, keeping them equal at every committed point.
  writer <- forkIO $ do
    let loop n = do
          s <- readIORef stop
          unless s $ do
            atomically $ do
              writeTVar t1 n; writeTVar t2 n; writeTVar t3 n; writeTVar t4 n
            loop (n + 1)
    loop 1
  -- Reader: a pure applicative fragment (no monadic bind) over four distinct
  -- reads -> exercises the readMany# batch.  All four must agree.
  let readBatch = (,,,) <$> readTVar t1 <*> readTVar t2 <*> readTVar t3 <*> readTVar t4
  replicateM_ 2000 $ do
    (a, b, c, d) <- atomically readBatch
    unless (a == b && b == c && c == d) $ do
      writeIORef stop True
      bail ("readMany-snapshot: torn batch " ++ show (a, b, c, d))
  writeIORef stop True
