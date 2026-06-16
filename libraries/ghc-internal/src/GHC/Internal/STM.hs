{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_HADDOCK not-home #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Internal.STM
--
-- The STM implementation that previously lived here was replaced by the
-- plan-based applicative STM in "GHC.Internal.Conc.STM".  This module is kept
-- as a thin re-export so existing importers (base's @GHC.Conc@\/@GHC.Conc.Sync@,
-- ghc-internal's @Conc.IO@\/@Conc.POSIX@\/@Conc.Windows@, @Event.Thread@, ...)
-- continue to resolve against the new implementation.
--
-- Note: unlike the old module, the @STM@ constructor is intentionally not
-- exported here — @STMPlan@ is an internal representation.
--
-----------------------------------------------------------------------------

module GHC.Internal.STM
        (
          -- * the 'STM' monad
          STM
        , atomically
        , retry
        , orElse
        , throwSTM
        , catchSTM
        , unsafeIOToSTM
          -- * TVars
        , TVar(..)
        , newTVar
        , newTVarIO
        , readTVar
        , readTVarIO
        , writeTVar
        ) where

import GHC.Internal.Conc.STM
