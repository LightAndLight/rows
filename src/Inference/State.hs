{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module Inference.State where

import Control.Concurrent.Supply (Supply, freshId)
import Control.Lens.Getter (uses, use)
import Control.Lens.Setter ((.=), (%=), (+=))
import Control.Lens.TH (makeLenses)
import Control.Monad.State (MonadState)
import Data.Sequence ((|>), Seq)

import Evidence
import Kind
import Meta
import Ty
data EvEntry a b c = EvEntry c (MetaT a Ty b) deriving Eq

data InferState a b c
  = InferState
  { _inferSupply :: Supply
  , _inferEvidence :: Seq (EvEntry a b c)
  , _inferKinds :: Meta a b -> Maybe (Kind a)
  , _inferDepth :: !Int -- ^ Quantification depth
  , _inferRank :: !Int -- ^ Lambda depth
  }
makeLenses ''InferState

newEv :: MonadState (InferState a b Int) m => MetaT a Ty b -> m (Ev Int x)
newEv ty = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferEvidence %= (|> EvEntry v ty)
  pure $ E v

deep :: MonadState (InferState a b c) m => m x -> m x
deep ma = do
  d <- use inferDepth <* (inferDepth += 1)
  ma <* (inferDepth .= d)

ranked :: MonadState (InferState a b c) m => m x -> m x
ranked ma = do
  r <- use inferRank <* (inferRank += 1)
  ma <* (inferRank .= r)
