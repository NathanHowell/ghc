-- Coverage for STM read-set validation: a pure applicative transaction over
-- several distinct reads must only ever return a *consistent* snapshot of all
-- TVars.  The reads are taken one at a time from live memory, but a torn
-- combination is rejected by the commit-time read-set validation, which restarts
-- the transaction onto a fresh snapshot.
--
-- A companion mid-flight zombie-abort test lives in stm_zombie_abort; it is
-- currently skipped pending the STM CPS validation rework (see its header).
module Main (main) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.IORef
import System.Exit (exitFailure)

bail :: String -> IO ()
bail msg = putStrLn msg >> exitFailure

main :: IO ()
main = do
  test_applicative_consistent_snapshot
  putStrLn "stm_validate: ok"

-- A pure applicative transaction with several distinct reads.  Against a writer
-- that keeps the four TVars mutually equal, every value 'atomically' returns
-- must be internally consistent (all four equal): the reads are taken one at a
-- time from live memory, but a torn combination is rejected by the commit-time
-- read-set validation, which restarts the transaction onto a fresh snapshot.
test_applicative_consistent_snapshot :: IO ()
test_applicative_consistent_snapshot = do
  t1 <- newTVarIO (0 :: Int)
  t2 <- newTVarIO (0 :: Int)
  t3 <- newTVarIO (0 :: Int)
  t4 <- newTVarIO (0 :: Int)
  done <- newIORef False
  -- Writer bumps all four together a bounded number of times, keeping them equal
  -- at every committed point, then signals completion.  Two things keep the test
  -- well-behaved: the writer is bounded *independently* of the reader (once it
  -- finishes, memory is static and the reader's next transaction commits
  -- trivially, so termination never depends on the reader winning a race), and a
  -- short delay between commits keeps contention light.  Without 'readMany#'s
  -- batched read, the applicative reader takes its four reads one at a time, so a
  -- maximally-tight writer would otherwise keep tearing the read set and starve
  -- the reader on restarts; the throttle leaves plenty of overlap to still
  -- exercise a read racing a concurrent commit.
  _ <- forkIO $ do
    let loop 0 = writeIORef done True
        loop n = do
          atomically $ do
            writeTVar t1 n; writeTVar t2 n; writeTVar t3 n; writeTVar t4 n
          threadDelay 50
          loop (n - 1)
    loop (1000 :: Int)
  -- Reader: a pure applicative transaction (no monadic bind) over four distinct
  -- reads, repeated until the writer finishes.  All four must agree in every
  -- returned result; a torn combination would mean commit-time validation let an
  -- inconsistent snapshot through.
  let readBatch = (,,,) <$> readTVar t1 <*> readTVar t2 <*> readTVar t3 <*> readTVar t4
      readLoop = do
        (a, b, c, d) <- atomically readBatch
        unless (a == b && b == c && c == d) $
          bail ("applicative-snapshot: torn result " ++ show (a, b, c, d))
        finished <- readIORef done
        unless finished readLoop
  readLoop
