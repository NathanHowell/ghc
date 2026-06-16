module Main (main) where

import Control.Concurrent.STM
import Control.Monad

sumTVars :: Int -> [TVar Int] -> STM Int
sumTVars n tvars =
  foldM (\acc tv -> do v <- readTVar tv; return (acc + v)) 0 (take n tvars)

main :: IO ()
main = do
  let n1 = 64
      n2 = 65
  tvars <- atomically $ replicateM n2 (newTVar 1)
  s1 <- atomically (sumTVars n1 tvars)
  when (s1 /= n1) $
    error ("stm_large_log: expected " ++ show n1 ++ " got " ++ show s1)
  s2 <- atomically (sumTVars n2 tvars)
  when (s2 /= n2) $
    error ("stm_large_log: expected " ++ show n2 ++ " got " ++ show s2)
