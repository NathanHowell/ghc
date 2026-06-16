-- M-10: a 2+-deep nested orElse must register the wait-set *union* of every
-- branch, so a blocked transaction wakes when ANY single branch's TVar changes.
-- We build  l1 `orElse` (l2 `orElse` (l3 `orElse` l4))  where each branch reads
-- its own always-False TVar and retries, then drive each of the four TVars
-- independently and require a wake every time.  Every wake is guarded by a
-- timeout so a dropped registration (the C-3 family at depth) fails
-- deterministically rather than hanging.
module Main (main) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import System.Exit (exitFailure)
import System.Timeout
import GHC.Conc (unsafeIOToSTM)

timeoutUs :: Int
timeoutUs = 5 * 1000000

bail :: String -> IO ()
bail msg = putStrLn msg >> exitFailure

-- One branch reading TVar `t`: succeeds with `name` once `t` is True, otherwise
-- (the first time it is evaluated) signals readiness and retries.
branch :: TVar Bool -> String -> MVar () -> STM String
branch t name fired = do
  v <- readTVar t
  if v
    then return name
    else do
      unsafeIOToSTM (void (tryPutMVar fired ()))
      retry

main :: IO ()
main = do
  forM_ [1 .. 4 :: Int] $ \k -> do
    t1 <- newTVarIO False
    t2 <- newTVarIO False
    t3 <- newTVarIO False
    t4 <- newTVarIO False
    let tvars = [t1, t2, t3, t4]
        names = ["b1", "b2", "b3", "b4"]
        target = tvars !! (k - 1)
        targetName = names !! (k - 1)
    -- Each branch needs its own readiness signal; we only require that the
    -- *whole* nest has reached its blocked state, which is true once the
    -- left-most branch (always evaluated first) has fired.
    ready <- newEmptyMVar
    done  <- newEmptyMVar
    let txn = branch t1 "b1" ready
                `orElse` (branch t2 "b2" ready
                  `orElse` (branch t3 "b3" ready
                    `orElse` branch t4 "b4" ready))
    _ <- forkIO $ do
          r <- atomically txn
          putMVar done r
    reached <- timeout timeoutUs (takeMVar ready)
    case reached of
      Nothing -> bail ("depth-case " ++ show k ++ ": nest never blocked")
      Just () -> return ()
    -- Wake by flipping ONLY the k-th branch's TVar.
    atomically (writeTVar target True)
    m <- timeout timeoutUs (takeMVar done)
    case m of
      Nothing -> bail ("depth-case " ++ show k
                       ++ ": LOST WAKEUP writing " ++ targetName)
      Just r
        | r == targetName -> return ()
        | otherwise       -> bail ("depth-case " ++ show k
                                   ++ ": woke with wrong branch " ++ show r
                                   ++ ", expected " ++ targetName)
  putStrLn "stm_nested_orElse: all nested branches woke on their own TVar"
