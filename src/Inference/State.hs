{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module Inference.State where

import Control.Concurrent.Supply (Supply, freshId)
import Control.Lens.Getter (uses, use)
import Control.Lens.Setter ((.=), (%=), (+=))
import Control.Lens.TH (makeLenses)
import Control.Monad.State (MonadState)
import Data.Foldable (find)
import Data.Sequence ((<|), (|>), ViewL(..), Seq)

import qualified Data.Sequence as Seq

import Evidence
import Kind
import Meta
import Tm
import Ty

data EvEntry meta tyVar tmVar
  = EvEntry
  { _evPlaceholder :: Placeholder
  , _evEvidence :: EvT (Tm (Meta 'Check meta tyVar)) tmVar
  , _evType :: MetaT 'Check meta Ty tyVar
  } deriving Eq

data InferState meta tyVar tmVar
  = InferState
  { _inferSupply :: Supply
  , _inferEvidence :: Seq (EvEntry meta tyVar tmVar)
  , _inferKinds :: Meta 'Check meta tyVar -> Maybe (Kind meta)
  , _inferDepth :: !Int -- ^ Quantification depth
  , _inferRank :: !Int -- ^ Lambda depth
  }
makeLenses ''InferState

updateEvidence ::
  MonadState (InferState meta tyVar tmVar) m =>
  Placeholder ->
  EvT (Tm (Meta 'Check meta tyVar)) tmVar ->
  MetaT 'Check meta Ty tyVar ->
  m ()
updateEvidence ph' evTm evTy = inferEvidence %= go
  where
    go es =
      case Seq.viewl es of
        EmptyL -> mempty
        ee@(EvEntry ph _ _) :< ees ->
           if ph == ph'
           then EvEntry ph evTm evTy <| ees
           else ee <| go ees

lookupEvidence ::
  MonadState (InferState meta tyVar tmVar) m =>
  Placeholder ->
  m (EvEntry meta tyVar tmVar)
lookupEvidence ph = do
  evs <- use inferEvidence
  case find ((== ph) . _evPlaceholder) evs of
    Nothing -> error "lookupEvidence: not found"
    Just ev -> pure ev

newPlaceholder ::
  MonadState (InferState meta tyVar tmVar) m =>
  MetaT 'Check meta Ty tyVar ->
  m (Ev x)
newPlaceholder ty = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  let p = Placeholder v
  inferEvidence %= (|> EvEntry p (EvT . pure $ P p) ty)
  pure $ P p

removePlaceholder ::
  MonadState (InferState meta tyVar tmVar) m =>
  Placeholder ->
  m ()
removePlaceholder ph = inferEvidence %= Seq.filter (\(EvEntry ph' _ _) -> ph /= ph')

deep :: MonadState (InferState a b c) m => m x -> m x
deep ma = do
  d <- use inferDepth <* (inferDepth += 1)
  ma <* (inferDepth .= d)

ranked :: MonadState (InferState a b c) m => m x -> m x
ranked ma = do
  r <- use inferRank <* (inferRank += 1)
  ma <* (inferRank .= r)
