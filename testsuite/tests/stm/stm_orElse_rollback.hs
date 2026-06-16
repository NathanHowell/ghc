module Main (main) where

import Control.Concurrent.STM
import Control.Monad

main :: IO ()
main = do
  tv <- newTVarIO (0 :: Int)
  r <- atomically $ do
    _ <- readTVar tv
    orElse
      (writeTVar tv 99 >> retry)
      (readTVar tv)
  when (r /= 0) $
    error ("stm_orElse_rollback: expected 0 got " ++ show r)
