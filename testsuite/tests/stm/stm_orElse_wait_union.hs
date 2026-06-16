module Main (main) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import System.Timeout

main :: IO ()
main = do
  a <- newTVarIO False
  b <- newTVarIO False
  ready <- newEmptyMVar
  done <- newEmptyMVar
  let left = do
        v <- readTVar a
        if v then return "A" else retry
      right = do
        v <- readTVar b
        if v then return "B" else do
          unsafeIOToSTM $ void $ tryPutMVar ready ()
          retry
  _ <- forkIO $ do
    r <- atomically (left `orElse` right)
    putMVar done r
  readyResult <- timeout (2 * 1000000) (takeMVar ready)
  case readyResult of
    Nothing -> error "orElse did not reach right-branch retry"
    Just () -> return ()
  atomically $ writeTVar b True
  m <- timeout (2 * 1000000) (takeMVar done)
  case m of
    Nothing -> error "orElse did not wake on right branch"
    Just "B" -> return ()
    Just other -> error ("unexpected orElse result: " ++ other)
