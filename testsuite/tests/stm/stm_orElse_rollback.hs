-- M-9: strengthen the rollback test.
--   (1) read-after: confirm a write discarded by an orElse retry does not leak
--       past `atomically` into shared memory (the original only checked the
--       value *within* the transaction).
--   (2) deterministic exactly-once conflict re-run: a transaction that conflicts
--       exactly once must re-run exactly once and observe the committed value -
--       distinguishing a correct conflict restart from a balanced lost update,
--       which `stm_stress` cannot.
--   (3) async exception mid-transaction: a throwTo delivered while a transaction
--       is blocked in `retry` must abort it cleanly and roll back its writes.
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
  test_rollback_no_leak
  test_inner_value_discarded
  test_exactly_once_conflict
  test_async_abort_rollback
  putStrLn "stm_orElse_rollback: ok"

-- (1) The left branch writes 99 then retries; orElse discards it and runs the
-- right branch.  After `atomically` the TVar must still read 0 in *shared*
-- memory: the discarded write must not have leaked out of the transaction.
test_rollback_no_leak :: IO ()
test_rollback_no_leak = do
  tv <- newTVarIO (0 :: Int)
  r <- atomically $ do
    _ <- readTVar tv
    orElse
      (writeTVar tv 99 >> retry)
      (readTVar tv)
  when (r /= 0) $ bail ("rollback-no-leak: in-txn value " ++ show r ++ " /= 0")
  -- The load-bearing extra check M-9 asks for: read AFTER atomically.
  after <- readTVarIO tv
  when (after /= 0) $
    bail ("rollback-no-leak: discarded write LEAKED, tv=" ++ show after)

-- A nested orElse: the inner left writes and retries, the inner right writes a
-- different value and succeeds; the outer must see the inner-right write only,
-- and nothing must leak from the discarded inner-left branch.
test_inner_value_discarded :: IO ()
test_inner_value_discarded = do
  tv <- newTVarIO (0 :: Int)
  r <- atomically $
    orElse (writeTVar tv 11 >> retry)
           (orElse (writeTVar tv 22 >> retry)
                   (do writeTVar tv 33; readTVar tv))
  when (r /= 33) $ bail ("inner-discarded: result " ++ show r ++ " /= 33")
  after <- readTVarIO tv
  when (after /= 33) $ bail ("inner-discarded: committed " ++ show after ++ " /= 33")

-- (2) Deterministic exactly-once conflict re-run.  The transaction reads `tv`,
-- then blocks (via an MVar handshake driven from unsafeIOToSTM) so a writer can
-- commit a conflicting change underneath it exactly once.  The transaction must
-- (a) re-run, (b) observe the new committed value on the second pass, and (c)
-- run its body exactly twice (once doomed, once successful) - no more, no less.
test_exactly_once_conflict :: IO ()
test_exactly_once_conflict = do
  tv       <- newTVarIO (0 :: Int)
  attempts <- newIORef (0 :: Int)
  gateOnce <- newIORef True          -- only stall on the very first attempt
  conflictReady <- newEmptyMVar      -- txn -> writer: "I have read the old value"
  conflictDone  <- newEmptyMVar      -- writer -> txn: "I have committed"
  let txn = do
        n <- unsafeIOToSTM $ do
               modifyIORef' attempts (+ 1)
               readIORef attempts
        v <- readTVar tv
        -- On the first attempt only, hand control to the writer and wait for it
        -- to commit a conflict, guaranteeing this attempt is doomed.
        when (n == 1) $ unsafeIOToSTM $ do
          stall <- readIORef gateOnce
          when stall $ do
            writeIORef gateOnce False
            putMVar conflictReady ()
            takeMVar conflictDone
        return v
  -- Writer: wait for the txn's first read, then commit tv := 7.
  writer <- forkIO $ do
    takeMVar conflictReady
    atomically (writeTVar tv 7)
    putMVar conflictDone ()
  res <- timeout timeoutUs (atomically txn)
  case res of
    Nothing -> bail "exactly-once-conflict: timed out (no re-run?)"
    Just v  -> do
      when (v /= 7) $ bail ("exactly-once-conflict: observed " ++ show v ++ " /= 7")
      n <- readIORef attempts
      when (n /= 2) $
        bail ("exactly-once-conflict: expected exactly 2 attempts, got " ++ show n)
  killThread writer

-- (3) Async exception mid-transaction.  A thread blocks in `retry`; we throwTo
-- it while it is parked, then verify (a) the exception was delivered and (b) any
-- write the doomed transaction performed before retrying did not leak.
test_async_abort_rollback :: IO ()
test_async_abort_rollback = do
  tv     <- newTVarIO (0 :: Int)
  parked <- newEmptyMVar           -- txn signals it has reached retry
  caught <- newEmptyMVar
  let txn = do
        writeTVar tv 123           -- a write that must be rolled back on abort
        unsafeIOToSTM (void (tryPutMVar parked ()))
        retry
  worker <- forkIO $
    (atomically txn >> return ())
      `catch` \e -> putMVar caught (e :: SomeException)
  reached <- timeout timeoutUs (takeMVar parked)
  case reached of
    Nothing -> bail "async-abort: transaction never reached retry"
    Just () -> return ()
  -- Give the thread a beat to actually block on the registered wait set, then
  -- deliver the async exception.
  threadDelay 200000
  throwTo worker (ErrorCall "async-abort")
  got <- timeout timeoutUs (takeMVar caught)
  case got of
    Nothing -> bail "async-abort: exception was not delivered (txn not interruptible?)"
    Just _  -> return ()
  after <- readTVarIO tv
  when (after /= 0) $
    bail ("async-abort: aborted write LEAKED, tv=" ++ show after)
