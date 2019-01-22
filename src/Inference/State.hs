{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module Inference.State where

import Control.Applicative ((<|>))
import Control.Concurrent.Supply (Supply, freshId)
import Control.Lens.Getter (uses)
import Control.Lens.Setter ((.=), (%=))
import Control.Lens.TH (makeLenses)
import Control.Monad.State (MonadState)
import Data.Sequence ((|>), Seq)
import Data.Void (Void)

import Evidence
import Kind
import Meta
import Ty

data EvEntry a b c
  = EvEntry c (MetaT a Ty b)

data InferState a b c
  = InferState
  { _inferSupply :: Supply
  , _inferEvidence :: Seq (EvEntry a b c)
  , _inferKinds :: Meta a b -> Maybe (Kind Void)
  }
makeLenses ''InferState

newEv :: MonadState (InferState a b Int) m => MetaT a Ty b -> m (Ev Int x)
newEv ty = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferEvidence %= (|> EvEntry v ty)
  pure $ E v

newMeta :: MonadState (InferState Int b c) m => Kind Void -> m (Meta Int b)
newMeta kind = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferKinds %=
    \f x ->
      f x <|>
      foldMeta (\y -> if y == v then Just kind else Nothing) (const Nothing) x
  pure $ M v

