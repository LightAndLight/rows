{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module Inference.State where

import Control.Applicative ((<|>))
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

data EvEntry a b c
  = EvEntry c (MetaT a Ty b)

data InferState a b c
  = InferState
  { _inferSupply :: Supply
  , _inferEvidence :: Seq (EvEntry a b c)
  , _inferKinds :: Meta a b -> Maybe (Kind a)
  , _inferDepth :: !Int -- ^ Binder depth
  }
makeLenses ''InferState

newEv :: MonadState (InferState a b Int) m => MetaT a Ty b -> m (Ev Int x)
newEv ty = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferEvidence %= (|> EvEntry v ty)
  pure $ E v

newMeta :: MonadState (InferState Int b c) m => Kind Int -> m (Meta Int b)
newMeta kind = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferKinds %=
    \f x ->
      f x <|>
      foldMeta
        (\_ y -> if y == v then Just kind else Nothing)
        (\_ -> const Nothing)
        (const Nothing)
        x
  d <- use inferDepth
  pure $ M d v

newSkolem :: MonadState (InferState Int b c) m => Kind Int -> m (Meta Int b)
newSkolem kind = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferKinds %=
    \f x ->
      f x <|>
      foldMeta
        (\_ -> const Nothing)
        (\_ y -> if y == v then Just kind else Nothing)
        (const Nothing)
        x
  d <- use inferDepth
  pure $ S d v

deep :: MonadState (InferState a b c) m => m x -> m x
deep ma = do
  d <- use inferDepth <* (inferDepth += 1)
  ma <* (inferDepth .= d)
