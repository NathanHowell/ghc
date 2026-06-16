{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.Word

nextWord64 :: Word64 -> Word64
nextWord64 s = s * 6364136223846793005 + 1442695040888963407

step :: Word64 -> (Word64, Word64)
step s = let s' = nextWord64 s in (s', s')

main :: IO ()
main = do
  let nTvars = 8
      nThreads = 4
      iters = 5000
      expected = nThreads * iters * 2
  tvars <- atomically $ replicateM nTvars (newTVar (0 :: Int))
  done <- newEmptyMVar
  forM_ [0 .. nThreads - 1] $ \tid -> forkIO $ do
    let seed = 0x9e3779b97f4a7c15 + fromIntegral tid
        go !s !n
          | n <= 0 = putMVar done ()
          | otherwise =
              let (w1, s1) = step s
                  (w2, s2) = step s1
                  i = fromIntegral (w1 `mod` fromIntegral nTvars)
                  j = fromIntegral (w2 `mod` fromIntegral nTvars)
              in do
                atomically $ do
                  let tvi = tvars !! i
                      tvj = tvars !! j
                  vi <- readTVar tvi
                  vj <- readTVar tvj
                  writeTVar tvi (vi + 1)
                  writeTVar tvj (vj + 1)
                go s2 (n - 1)
    go seed iters
  replicateM_ nThreads (takeMVar done)
  total <- atomically $ foldM (\acc tv -> do v <- readTVar tv; return (acc + v)) 0 tvars
  when (total /= expected) $
    error ("STM stress failed: total=" ++ show total ++ " expected=" ++ show expected)
