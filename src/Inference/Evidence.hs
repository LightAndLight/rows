{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Inference.Evidence where

import Bound.Scope (abstract)
import Control.Lens.Getter (use)
import Control.Lens.Wrapped (_Wrapped)
import Control.Monad (void, join, guard)
import Control.Monad.Except (throwError)
import Data.Bifunctor (bimap)
import Data.Set (Set)

import qualified Data.Set as Set

import Data.List.Utils (anyA, allA, findM)
import Evidence
import Inference.State
import Inference.Type.Error
import Inference.Type.Monad
import Meta
import Tm
import Ty

-- | Match two predicate heads
--
-- I think later down the track we'll want to do unification here
matchHead
  :: Eq tyVar
  => MetaT 'Check Int Ty tyVar -- ^ Desired head
  -> MetaT 'Check Int Ty tyVar -- ^ Actual head
  -> TypeM s tyVar tmVar Bool
matchHead desired actual =
  let
    (dCount, dHead, dArgs) = unfoldApps $ unMetaT desired
    (aCount, aHead, aArgs) = unfoldApps $ unMetaT actual
  in
  if dHead == aHead && dCount == aCount
    then allA (\(d, a) -> pure $ d == a) $ zip dArgs aArgs
    else pure False

-- |
-- Entailment
--
-- @||- (l | {})@
--
-- @(l | r) ||- (l | (l' | r))    (l <= l')@
--
-- @(l | r) ||- (l | (l' | r))    (l > l')@
--
-- @A ||- A@
entails
  :: (Ord tyVar, Show tyVar)
  => [MetaT 'Check Int Ty tyVar]
  -> MetaT 'Check Int Ty tyVar
  -> TypeM s tyVar tmVar ()
entails tys ty =
  case unMetaT ty of
    TyApp TyOffset{} TyRowEmpty -> pure ()
    TyApp (TyOffset l) (TyApp (TyApp TyRowExtend{} _) rest) ->
      entails tys $ MetaT (TyApp (TyOffset l) rest)
    _ -> do
      dTy <- displayType ty
      dTys <- traverse displayType tys
      void $
        maybe (throwError $ TypeCannotDeduce dTy dTys) pure =<<
        findM (matchHead ty) tys

-- |
-- Evidence construction
--
-- @||- 0 : (l | {})@
--
-- @p : (l | r) ||- p : (l | (l' | r))    (l <= l')@
--
-- @p : (l | r) ||- p : (l | (l' | r))    (l > l')@
--
-- @p : A ||- p : A@
constructEvidence ::
  (Ord tyVar, Show tyVar) =>
  Bool -> -- ^ Can we introduce new constraints?
  MetaT 'Check Int Ty tyVar -> -- ^ Type for which we construct evidence
  TypeM s tyVar tmVar (Bool, EvT (Tm (Meta 'Check Int tyVar)) tmVar)
constructEvidence canIntro evTy =
  case unMetaT evTy of
    TyApp TyOffset{} TyRowEmpty -> pure (False, EvT $ TmInt 0)
    TyApp (TyOffset l) (TyApp (TyApp (TyRowExtend l') _) rest) -> do
      (more, evTm) <- constructEvidence canIntro $ MetaT (tyOffset l rest)
      pure $
        if l < l'
        then (more, evTm)
        else (more, EvT $ TmAdd (TmInt 1) (unEvT evTm))
    _ -> do
      mFound <-
        findM (\(EvEntry _ _ evTy') -> matchHead evTy evTy') =<<
        use inferEvidence
      case mFound of
        Nothing ->
          if canIntro
          then (,) True . EvT . TmVar <$> newPlaceholder evTy
          else do
            dTy <- displayType evTy
            dTys <-
              foldr
                (\(EvEntry _ _ evTy') rest ->
                   (:) <$> displayType evTy' <*> rest)
                (pure []) =<<
              use inferEvidence
            throwError $ TypeCannotDeduce dTy dTys
        Just (EvEntry _ evTm _) -> pure (False, evTm)

substM :: (Monad f, Monad m, Traversable m) => (a -> f (m b)) -> m a -> f (m b)
substM f = fmap join . traverse f

solvePlaceholders ::
  forall tyVar x s tmVar.
  (Ord tyVar, Show tyVar) =>
  (tmVar -> x) ->
  EvT (Tm (Meta 'Check Int tyVar)) x ->
  TypeM s tyVar tmVar (EvT (Tm (Meta 'Check Int tyVar)) x)
solvePlaceholders ctx = _Wrapped (substM go)
  where
    go :: Ev x -> TypeM s tyVar tmVar (Tm (Meta 'Check Int tyVar) (Ev x))
    go (V v) = pure $ pure (V v)
    go (P ph) = do
      EvEntry _ _ evTy <- lookupEvidence ph

      evTy' <- findType evTy
      (more, evTm') <- constructEvidence True evTy'
      updateEvidence ph evTm' evTy'

      let evTm'' = ctx <$> evTm'
      if more
        then unEvT <$> solvePlaceholders ctx evTm''
        else pure $ unEvT evTm''

abstractEvidence ::
  forall tyVar x s tmVar.
  (Show tyVar, Ord tyVar) =>
  EvT (Tm (Meta 'Check Int tyVar)) x ->
  TypeM s tyVar tmVar
    ( EvT (Tm (Meta 'Check Int tyVar)) x
    , [MetaT 'Check Int Ty tyVar]
    )
abstractEvidence (EvT tm) = do
  (placeholders, vars) <- listify tm

  rank <- use inferRank
  constraints <- constraintsFor (Rank rank) placeholders vars

  (tm', constraints') <- abstractPlaceholders constraints tm

  pure (EvT tm', constraints')

  where
    listify ::
      Tm (Meta 'Check Int tyVar) (Ev x) ->
      TypeM s tyVar tmVar (Set Placeholder, [Ev x])
    listify =
      foldr
        (\a b ->
            case a of
              P ph -> bimap (Set.insert ph) (a :) <$> b
              _ -> b)
        (pure (Set.empty, []))

    constraintsFor ::
      Rank ->
      Set Placeholder ->
      [Ev x] ->
      TypeM s tyVar tmVar [(Placeholder, MetaT 'Check Int Ty tyVar)]
    constraintsFor _ _ [] = pure []
    constraintsFor rank phs (ev:evs) =
      case ev of
        P ph | ph `Set.member` phs -> do
          EvEntry _ _ evTy <- lookupEvidence ph

          defer <- anyA (fmap (maybe False (< rank)) . metaRank) (unMetaT evTy)
          if defer
            then constraintsFor rank (Set.delete ph phs) evs
            else ((ph, evTy) :) <$> constraintsFor rank (Set.delete ph phs) evs
        _ -> constraintsFor rank phs evs

    abstractPlaceholders
      :: [(Placeholder, MetaT 'Check Int Ty tyVar)]
      -> Tm (Meta 'Check Int tyVar) (Ev x)
      -> TypeM s tyVar tmVar (Tm (Meta 'Check Int tyVar) (Ev x), [MetaT 'Check Int Ty tyVar])
    abstractPlaceholders [] t = pure (t, [])
    abstractPlaceholders ((ph, ty) : rest) t = do
      removePlaceholder ph
      bimap
        (TmLam . abstract (foldEv (guard . (== ph)) (const Nothing)))
        (ty :) <$>
        abstractPlaceholders rest t
