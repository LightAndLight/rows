{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language RankNTypes #-}
module Inference.Type where

import Bound.Scope (abstractEither, fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Concurrent.Supply (Supply)
import Control.Lens.Getter (use)
import Control.Lens.Review ((#))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, evalStateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Strict (runWriterT)
import Data.Bifunctor (first)
import Data.Coerce (coerce)
import Data.Equivalence.Monad (MonadEquiv, equate, runEquivT)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.Void (Void, absurd)

import qualified Data.Set as Set

import Evidence
import Inference.Evidence
import Inference.Kind
import Inference.State
import Inference.Type.Error
import Inference.Type.Row
import Kind
import Meta
import Tm
import Ty

occursType :: Eq meta => meta -> MetaT meta Ty a -> Bool
occursType v =
  foldr
    (\a b -> foldMeta (== v) (const False) a || b)
    False .
    unMetaT

combineType
  :: (Show a, Show b, Ord a, Eq b)
  => MetaT a Ty b
  -> MetaT a Ty b
  -> MetaT a Ty b
combineType (MetaT x) (MetaT y) = MetaT $ go x y
  where
    go TyArr TyArr = TyArr
    go TyRowEmpty TyRowEmpty = TyRowEmpty
    go TyRecord TyRecord = TyRecord
    go TyVariant TyVariant = TyVariant
    go (TyRowExtend l) (TyRowExtend l') | l == l' = TyRowExtend l
    go (TyCtor s) (TyCtor s') | s == s' = TyCtor s
    go (TyVar (N a)) (TyVar (N b)) | a == b = TyVar (N b)
    go (TyVar (M a)) (TyVar (M b)) = TyVar $ M (min a b)
    go (TyApp a b) (TyApp a' b') = TyApp (go a a') (go b b')
    go (TyVar M{}) b = b
    go a (TyVar M{}) = a
    go _ _ =
      error $
      "combineType: combining un-unifiable terms\n\n" <>
      show x <>
      "\n\n" <>
      show y

unifyType
  :: forall tmVar tyVar ev c m
   . ( MonadError (TypeError Int tyVar tmVar) m
     , MonadState (InferState Int tyVar ev) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar, Show tyVar
     )
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> MetaT Int Ty tyVar
  -> MetaT Int Ty tyVar
  -> m ()
unifyType tyCtorCtx x y = do
  supply <- use inferSupply
  tyVarCtx <- use inferKinds
  x' <- unMetaT <$> findType x
  y' <- unMetaT <$> findType y
  xKind <- evalStateT (inferKind tyCtorCtx tyVarCtx x') supply
  yKind <- evalStateT (inferKind tyCtorCtx tyVarCtx y') supply
  if xKind == yKind
    then go x' y'
    else throwError $ _TypeKindMismatch # (MetaT x', absurd <$> xKind, MetaT y', absurd <$> yKind)
  where
    go :: Ty (Meta Int tyVar) -> Ty (Meta Int tyVar) -> m ()
    go TyArr TyArr = pure ()
    go TyRowEmpty TyRowEmpty = pure ()
    go TyRecord TyRecord = pure ()
    go TyVariant TyVariant = pure ()
    go (TyRowExtend l) (TyRowExtend l') | l == l' = pure ()
    go ty@(TyApp (TyApp (TyRowExtend l) t) r) s = do
      rewritten <- rewriteRow tyCtorCtx (rowTail r) l s
      case rewritten of
        Just (_, t', r') ->
          unifyType tyCtorCtx (MetaT t) (MetaT t') *>
          unifyType tyCtorCtx (MetaT r) (MetaT r')
        Nothing -> throwError $ TypeMismatch (MetaT ty) (MetaT s)
    go s t@(TyApp (TyApp TyRowExtend{} _) _) = go t s
    go (TyCtor s) (TyCtor s') | s == s' = pure ()
    go (TyVar (N a)) (TyVar (N b)) | a == b = pure ()
    go ty@(TyVar M{}) ty'@(TyVar M{}) = equate (MetaT ty) (MetaT ty')
    go (TyApp a b) (TyApp a' b') =
      unifyType tyCtorCtx (MetaT a) (MetaT a') *>
      unifyType tyCtorCtx (MetaT b) (MetaT b')
    go ty'@(TyVar (M a)) ty =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else equate (MetaT ty') (MetaT ty)
    go ty ty'@(TyVar (M a)) =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else equate (MetaT ty) (MetaT ty')
    go l m = throwError $ TypeMismatch (MetaT l) (MetaT m)

generalize :: MetaT Int Ty tyVar -> Forall tyVar
generalize (MetaT t) =
  Forall (Set.size uniq) $
  abstractEither
    (foldMeta (Left . fromJust . (`elemIndex` ordered uniq metas)) Right)
    t
  where
    ordered set xs =
      case xs of
        [] -> []
        a:as ->
          if a `Set.member` set
          then a : ordered (Set.delete a set) as
          else ordered set as

    (uniq, metas) =
      foldr
        (\a (b1, b2) -> foldMeta ((,) <$> (`Set.insert` b1) <*> (: b2)) (const (b1, b2)) a)
        (Set.empty, [])
        t

generalizeType
  :: forall tyVar tmVar c x m
   . ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar
     , Show tyVar, Show tmVar
     , Show x
     )
  => (EvT Int (Tm (Meta Int tyVar)) x, MetaT Int Ty tyVar)
  -> m (Tm Void x, Forall tyVar)
generalizeType (EvT tm, MetaT ty) = do
  (tm', constraints) <- finalizeEvidence tm
  ty' <-
    generalize <$>
    findType (MetaT $ foldr (tyConstraint . unMetaT) ty constraints)
  pure (stripAnnots tm', ty')

applyEvidence
  :: ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Show tyVar, Show x
     )
  => [MetaT Int Ty tyVar]
  -> EvT Int (Tm (Meta Int tyVar)) x
  -> m (EvT Int (Tm (Meta Int tyVar)) x)
applyEvidence [] !a = pure a
applyEvidence (p:ps) (EvT !a) = do
  res <- fmap fst . runWriterT $ evidenceFor p
  EvT e <- maybe (EvT . TmVar <$> newEv p) pure res
  applyEvidence ps $ EvT (TmApp a e)

inferTypeM
  :: ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Ord tyVar, Show tyVar, Show x
     )
  => (tmVar -> x)
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (x -> Either tmVar (MetaT Int Ty tyVar))
  -> EvT Int (Tm (Meta Int tyVar)) x
  -> m (EvT Int (Tm (Meta Int tyVar)) x, MetaT Int Ty tyVar)
inferTypeM ctx tyCtorCtx varCtx tm =
  case unEvT tm of
    TmAnn a ty -> do
      (EvT tm', aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      unifyType tyCtorCtx aTy (MetaT ty)
      pure (EvT $ TmAnn tm' ty, MetaT ty)
    TmVar E{} -> error "trying to infer type for evidence variable"
    TmVar (V a) -> do
      ty <- either (throwError . TypeVarNotFound) pure $ varCtx a
      let (ty', constraints) = coerce (stripConstraints $ unMetaT ty)
      tm' <- applyEvidence constraints tm
      pure (tm', ty')
    TmApp a b -> do
      (EvT a', aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      (EvT b', MetaT bTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT b
      retTy <- newMeta KindType
      unifyType
        tyCtorCtx
        aTy
        (MetaT $ TyApp (TyApp TyArr bTy) (TyVar retTy))
      pure (EvT $ TmApp a' b', MetaT $ TyVar retTy)
    TmAdd a b -> do
      (EvT a', aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      unifyType tyCtorCtx aTy (lift TyInt)
      (EvT b', bTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT b
      unifyType tyCtorCtx bTy (lift TyInt)
      pure (EvT $ TmAdd a' b', lift TyInt)
    TmLam s -> do
      argTy <- newMeta KindType
      (EvT body', bodyTy) <-
        inferTypeM
          (F . ctx)
          tyCtorCtx
          (unvar (const $ Right $ MetaT $ TyVar argTy) varCtx)
          (EvT $ sequence <$> fromScope s)
      pure
        ( EvT $ TmLam $ toScope $ sequence <$> body'
        , MetaT $ TyApp (TyApp TyArr (TyVar argTy)) (unMetaT bodyTy)
        )
    TmEmpty -> pure (EvT TmEmpty, lift $ tyRecord TyRowEmpty)
    TmSelect l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $ tyArr (tyRecord $ tyRowExtend l metaTy metaRow) metaTy
        )
    TmRestrict l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr (tyRecord $ tyRowExtend l metaTy metaRow) $
          tyRecord metaRow
        )
    TmExtend l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr metaTy $
          tyArr (tyRecord metaRow) $
          tyRecord (tyRowExtend l metaTy metaRow)
        )
    TmMatch l -> do
      metaA <- TyVar <$> newMeta KindType
      metaB <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr (tyVariant (tyRowExtend l metaA metaRow)) $
          tyArr (tyArr metaA metaB) $
          tyArr (tyArr (tyVariant metaRow) metaB) $
          metaB
        )
    TmInject l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr metaTy (tyVariant $ tyRowExtend l metaTy metaRow)
        )
    TmEmbed l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr metaRow (tyVariant $ tyRowExtend l metaTy metaRow)
        )
    TmInt n -> pure (EvT $ TmInt n, lift TyInt)

inferType
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar
     , Show tyVar
     , Show tmVar
     )
  => Supply -- ^ Name supply
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (tyVar -> Maybe (Kind Void)) -- ^ Type variables
  -> (tmVar -> Either tmVar (Ty tyVar)) -- ^ Term variables
  -> Tm tyVar tmVar
  -> m (Tm Void tmVar, Forall tyVar)
inferType supply tyCtorCtx tyVarCtx varCtx tm =
  runEquivT
    id
    combineType
    (evalStateT
       (generalizeType =<<
        inferTypeM
          id
          tyCtorCtx
          (fmap lift . varCtx)
          (lift $ first N tm))
       (InferState
        { _inferSupply = supply
        , _inferEvidence = mempty
        , _inferKinds = foldMeta (const Nothing) tyVarCtx
        }))
