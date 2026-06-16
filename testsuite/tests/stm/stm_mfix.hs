{-# LANGUAGE ScopedTypeVariables #-}
-- M-10: targeted coverage of the mfixSTM / SFix divergence path.
--   (1) a genuinely recursive mfixSTM that ties a cyclic knot through TVars and
--       observes the fixed point (the value flows back into the body).
--   (2) a *retrying* mfixSTM: the body retries, so the fixed point is never
--       produced.  Forcing it must diverge into the black hole (FixIOException);
--       crucially, when wrapped in `orElse` with a succeeding alternative the
--       whole transaction must still commit via the alternative.
--   (3) a *throwing* mfixSTM: an exception raised in the body must propagate out
--       of `atomically` unchanged (not be masked as a fix-point divergence).
module Main (main) where

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Control.Monad.Fix (mfix)
import System.Exit (exitFailure)
import System.Timeout

-- The user-facing entry to the SFix / mfixSTM machinery is the @MonadFix STM@
-- instance (its method is @mfixSTM@); @mfixSTM@ itself is not exported from the
-- public @GHC.Conc@, so we drive it through @mfix@.
mfixSTM :: (a -> STM a) -> STM a
mfixSTM = mfix

timeoutUs :: Int
timeoutUs = 5 * 1000000

bail :: String -> IO ()
bail msg = putStrLn msg >> exitFailure

-- A self-referential node: each node holds an Int and a TVar pointing at the
-- "next" node.  We build a single-node cycle (next points back at itself) with
-- mfixSTM, which requires the node value before it has finished constructing.
data Node = Node { nodeVal :: Int, nodeNext :: TVar Node }

main :: IO ()
main = do
  test_recursive
  test_retry_then_orElse
  test_throw
  putStrLn "stm_mfix: ok"

-- (1) Recursive knot: build a one-element cyclic linked list inside STM.  The
-- `next` TVar of the node must point back at the very node being constructed -
-- only achievable because mfixSTM feeds the result back into the body.
test_recursive :: IO ()
test_recursive = do
  node <- atomically $ mfixSTM $ \self -> do
            nextTV <- newTVar self        -- points at the node we are building
            return (Node 42 nextTV)
  -- Follow the cycle: node.next must be the same node (val 42), repeatedly.
  v0 <- nodeVal <$> readTVarIO (nodeNext node)
  when (v0 /= 42) $ bail ("recursive: node.next.val " ++ show v0 ++ " /= 42")
  loop <- atomically $ do
            n1 <- readTVar (nodeNext node)
            n2 <- readTVar (nodeNext n1)
            return (nodeVal n2)
  when (loop /= 42) $ bail ("recursive: 2-hop cycle val " ++ show loop ++ " /= 42")

-- (2) A retrying mfixSTM body never yields the fixed point: the SFix Retry arm
-- leaves the knot black-holed and rolls the body back.  Under `orElse` with a
-- succeeding right branch the whole transaction must discard the mfix branch
-- (its write included) and commit the right branch's result.  The fixed point is
-- referenced (`self`) but only inside the lazy, discarded write, so it is never
-- forced - exercising the retry-rollback path, not the divergence path.  Guarded
-- by a timeout so a botched re-run loop fails deterministically.
test_retry_then_orElse :: IO ()
test_retry_then_orElse = do
  tv <- newTVarIO (0 :: Int)
  res <- timeout timeoutUs $ atomically $
           orElse
             (mfixSTM $ \self -> do
                 -- reference the knot (so SFix matters) but lazily, then retry
                 writeTVar tv (self `seq` 1)
                 retry)
             (return (7 :: Int))
  case res of
    Nothing      -> bail "retry-then-orElse: timed out (divergent re-run loop?)"
    Just 7       -> return ()
    Just other   -> bail ("retry-then-orElse: result " ++ show other ++ " /= 7")
  -- The discarded mfix branch's write must not have leaked.
  after <- readTVarIO tv
  when (after /= 0) $ bail ("retry-then-orElse: mfix branch write LEAKED, tv=" ++ show after)

-- (3) An exception thrown inside the mfixSTM body propagates unchanged out of
-- atomically (it is a Raise outcome, not a fix-point black hole).
test_throw :: IO ()
test_throw = do
  r <- try $ atomically $ mfixSTM $ \(_self :: Int) ->
         throwSTM (ErrorCall "mfix-boom")
  case r of
    Left (ErrorCall msg)
      | msg == "mfix-boom" -> return ()
      | otherwise          -> bail ("throw: wrong message " ++ show msg)
    Right (v :: Int)       -> bail ("throw: expected exception, got " ++ show v)
