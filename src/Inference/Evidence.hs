{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Inference.Evidence where

import Bound.Scope (abstract)
import Control.Lens.Getter (use)
import Control.Lens.Setter ((.=))
import Control.Monad (void)
import Control.Monad.Except (throwError)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Strict (WriterT, runWriterT, tell)
import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Data.Sequence ((<|), Seq)
import Data.Traversable (for)

import qualified Data.Sequence as Seq

import Data.List.Utils (partitionM, anyA)
import Evidence
import Inference.State
import Inference.Type.Error
import Inference.Type.Monad
import Meta
import Tm
import Ty

findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
findM p =
  foldr
    (\a b -> p a >>= \x -> if x then pure (Just a) else b)
    (pure Nothing)

allA :: Applicative m => (a -> m Bool) -> [a] -> m Bool
allA p =
  foldr
    (\a b -> (&&) <$> p a <*> b)
    (pure True)

-- | Match two predicate heads
--
-- I think later down the track we'll want to do unification here
matchHead
  :: Eq tyVar
  => MetaT 'Check Int Ty tyVar -- ^ Desired head
  -> MetaT 'Check Int Ty tyVar -- ^ Actual head
  -> TypeM s tyVar tmVar ev Bool
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
  -> TypeM s tyVar tmVar ev ()
entails tys ty = do
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
evidenceFor
  :: (Ord tyVar, Show tyVar)
  => MetaT 'Check Int Ty tyVar
  -> WriterT
       (Seq (EvEntry Int tyVar Int))
       (TypeM s tyVar tmVar Int)
       (Maybe (EvT Int (Tm (Meta 'Check Int tyVar)) x))
evidenceFor ty = do
  ty' <- lift $ findType ty
  case unMetaT ty' of
    TyApp TyOffset{} TyRowEmpty -> pure . Just . EvT $ TmInt 0
    TyApp (TyOffset l) (TyApp (TyApp (TyRowExtend l') _) rest) -> do
      let super = MetaT $ TyApp (TyOffset l) rest
      res <- evidenceFor super
      e <-
        maybe
          (do
              e' <- newEv super
              tell [EvEntry (foldEv id undefined e') super]
              pure $ TmVar e')
          (pure . unEvT)
          res
      pure . Just . EvT $
        if l <= l'
        then e
        else TmAdd (TmInt 1) e
    _ -> pure Nothing

getEvidence
  :: forall s tyVar tmVar x
   . (Ord tyVar, Show tyVar)
  => TypeM s tyVar tmVar Int
       ( [(Int, EvT Int (Tm (Meta 'Check Int tyVar)) x)]
       , [(Int, MetaT 'Check Int Ty tyVar)]
       )
getEvidence = use inferEvidence >>= go
  where
    go
      :: Seq (EvEntry Int tyVar Int)
      -> TypeM s tyVar tmVar Int
           ( [(Int, EvT Int (Tm (Meta 'Check Int tyVar)) x)]
           , [(Int, MetaT 'Check Int Ty tyVar)]
           )
    go evs | Seq.null evs = pure mempty
    go evs = do
      (evs', more) <-
        runWriterT $
        for evs $ \(EvEntry e ty) ->
          maybe (Right (e, ty)) (Left . (,) e) <$> evidenceFor ty
      (partitionEithers (toList evs') <>) <$> go more

finalizeEvidence
  :: forall s tyVar tmVar x
   . ( Ord tyVar
     , Show tyVar, Show tmVar
     , Show x
     )
  => Tm (Meta 'Check Int tyVar) (Ev Int x)
  -> TypeM s tyVar tmVar Int (Tm (Meta 'Check Int tyVar) x, [MetaT 'Check Int Ty tyVar])
finalizeEvidence tm = do
  (sat, unsat) <- getEvidence
  rank <- Rank <$> use inferRank
  (now, defer) <-
    partitionM
      (anyA (fmap (maybe False (>= rank)) . metaRank) . unMetaT . snd)
      unsat
  let
    (unsatVals, unsatTypes) = unzip now
    tm' = tm >>= foldEv (\x -> maybe (pure $ E x) unEvT $ lookup x sat) (pure . V)
    tm'' =
      foldr
        (\a ->
           TmLam .
           abstract
             (foldEv
                (\x -> if x == a then Just () else Nothing)
                (const Nothing)))
        tm'
        unsatVals
  inferEvidence .= foldr (\(a, b) c -> EvEntry a b <| c) mempty defer
  either
    (\x -> error $ "un-abstracted evidence: " <> show x <> "\n\n" <> show unsatVals)
    (\x -> pure (x, unsatTypes))
    (traverse (foldEv Left Right) tm'')
