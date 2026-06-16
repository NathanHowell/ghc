module Main (main) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.IORef
import GHC.Conc (unsafeIOToSTM)
import System.Timeout

main :: IO ()
main = do
  tv <- newTVarIO False
  counter <- newIORef (0 :: Int)
  retried <- newEmptyMVar
  let txn = do
        unsafeIOToSTM $ modifyIORef' counter (+1)
        v <- readTVar tv
        if v then return () else do
          unsafeIOToSTM $ void $ tryPutMVar retried ()
          retry
  _ <- forkIO $ do
    takeMVar retried
    atomically $ writeTVar tv True
  result <- timeout (2 * 1000000) (atomically txn)
  case result of
    Nothing -> error "unsafeIOToSTM retry test timed out"
    Just () -> do
      n <- readIORef counter
      when (n < 2) $
        error ("unsafeIOToSTM did not rerun on retry: count=" ++ show n)
