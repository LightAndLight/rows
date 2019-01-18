{-# language FlexibleContexts #-}
{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Inference.Type where

import Bound.Scope (abstractEither, fromScope)
import Bound.Var (unvar)
import Control.Applicative ((<|>))
import Control.Concurrent.Supply (Supply, freshId)
import Control.Lens.Getter (use, uses)
import Control.Lens.TH (makeClassyPrisms, makeLenses)
import Control.Lens.Plated (plate)
import Control.Lens.Review ((#))
import Control.Lens.Setter ((%=), (.=))
import Control.Lens.Traversal (traverseOf)
import Control.Monad ((<=<))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, evalStateT)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (first)
import Data.Equivalence.Monad (MonadEquiv, equate, classDesc, runEquivT)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.Void (Void, absurd)

import qualified Data.Set as Set

import Inference.Kind
import Kind
import Label
import Meta
import Tm
import Ty

data InferState a b
  = InferState
  { _inferSupply :: Supply
  , _inferKinds :: Meta a b -> Maybe (Kind Void)
  }
makeLenses ''InferState

newMeta :: MonadState (InferState Int b) m => Kind Void -> m (Meta Int b)
newMeta kind = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferKinds %=
    \f x ->
      f x <|>
      foldMeta (\y -> if y == v then Just kind else Nothing) (const Nothing) x
  pure $ M v

data TypeError a b c
  = TypeOccurs a (MetaT a Ty b)
  | TypeMismatch (MetaT a Ty b) (MetaT a Ty b)
  | TypeVarNotFound c
  | TypeKindMismatch (MetaT a Ty b) (Kind Void) (MetaT a Ty b) (Kind Void)
  | TypeKindError (KindError (Meta Int b))
  deriving (Eq, Show)
makeClassyPrisms ''TypeError

instance AsKindError (TypeError a b c) (Meta Int b) where
  _KindError = _TypeKindError

occursType :: Eq meta => meta -> MetaT meta Ty a -> Bool
occursType v =
  foldr
    (\a b -> foldMeta (== v) (const False) a || b)
    False .
    unMetaT

rowTail :: Show a => Ty (Meta Int a) -> Ty (Meta Int a)
rowTail (TyApp (TyApp TyRowExtend{} _) r) = r
rowTail (TyVar v) = TyVar v

rowTail TyRowEmpty = TyRowEmpty
rowTail a =
  error $
  "rowTail: can't get tail of:\n\n" <>
  show a

rewriteRow
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , MonadState (InferState Int tyVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar, Show tyVar
     )
  => (String -> Maybe (Kind Void))
  -> Ty (Meta Int tyVar) -- ^ row tail
  -> Label -- ^ desired label
  -> Ty (Meta Int tyVar) -- ^ term to rewrite
  -> m (Maybe (Label, Ty (Meta Int tyVar), Ty (Meta Int tyVar)))
rewriteRow tyCtorCtx rt ll ty =
  case ty of
    TyApp (TyApp (TyRowExtend l) t) r ->
      if ll == l
      then -- row-head
        pure $ Just (l, t, r)
      else do -- row-swap
        res <- rewriteRow tyCtorCtx rt ll r
        pure $ case res of
          Just (l', t', r') -> Just (l', t', tyRowExtend l t r')
          Nothing -> Nothing
    TyVar M{} -> -- row-var
      if ty == rt
      then error "infinite record"
      else do
        metaTy <- TyVar <$> newMeta KindType
        metaRow <- TyVar <$> newMeta KindRow
        equate (MetaT ty) (MetaT $ tyRowExtend ll metaTy metaRow)
        pure $ Just (ll, metaTy, metaRow)
    _ -> pure Nothing

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
  :: forall tmVar tyVar c m
   . ( MonadError (TypeError Int tyVar tmVar) m
     , MonadState (InferState Int tyVar) m
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
    go (TyRowExtend l) (TyRowExtend l') | l == l' = pure ()
    go ty@(TyApp (TyApp (TyRowExtend l) t) r) s = do
      rewritten <- rewriteRow tyCtorCtx (rowTail r) l s
      case rewritten of
        Just (_, t', r') ->
          unifyType tyCtorCtx (MetaT t) (MetaT t') *>
          unifyType tyCtorCtx (MetaT r) (MetaT r')
        Nothing -> throwError $ TypeMismatch (MetaT ty) (MetaT s)
    go s t@(TyApp (TyApp TyRowExtend{} _) _) = go t s
    go TyRecord TyRecord = pure ()
    go TyVariant TyVariant = pure ()
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


findType
  :: MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
  => MetaT Int Ty tyVar
  -> m (MetaT Int Ty tyVar)
findType =
  fmap MetaT .
  traverseOf plate (fmap unMetaT . findType . MetaT) <=<
  fmap unMetaT . classDesc

generalize :: Ty (Meta Int tyVar) -> Forall tyVar
generalize t =
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
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar
     )
  => MetaT Int Ty tyVar
  -> m (Forall tyVar)
generalizeType = fmap generalize . fmap unMetaT . findType

inferTypeM
  :: ( MonadState (InferState Int tyVar) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar, Show tyVar
     )
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (x -> Either tmVar (MetaT Int Ty tyVar))
  -> Tm (Meta Int tyVar) x
  -> m (MetaT Int Ty tyVar)
inferTypeM tyCtorCtx varCtx tm =
  case tm of
    TmAnn a ty -> do
      aTy <- inferTypeM tyCtorCtx varCtx a
      unifyType tyCtorCtx aTy (MetaT ty)
      pure $ MetaT ty
    TmVar a ->
      either (throwError . TypeVarNotFound) pure $ varCtx a
    TmApp a b -> do
      aTy <- inferTypeM tyCtorCtx varCtx a
      bTy <- unMetaT <$> inferTypeM tyCtorCtx varCtx b
      retTy <- newMeta KindType
      unifyType
        tyCtorCtx
        aTy
        (MetaT $ TyApp (TyApp TyArr bTy) (TyVar retTy))
      pure $ MetaT $ TyVar retTy
    TmLam s -> do
      argTy <- newMeta KindType
      bodyTy <-
        inferTypeM
          tyCtorCtx
          (unvar (const $ Right $ MetaT $ TyVar argTy) varCtx)
          (fromScope s)
      pure . MetaT $ TyApp (TyApp TyArr (TyVar argTy)) (unMetaT bodyTy)
    TmEmpty -> pure . lift $ tyRecord TyRowEmpty
    TmSelect l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      pure . MetaT $ tyArr (tyRecord $ tyRowExtend l metaTy metaRow) metaTy
    TmRestrict l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      pure . MetaT $
        tyArr (tyRecord $ tyRowExtend l metaTy metaRow) (tyRecord metaRow)
    TmExtend l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      pure . MetaT $
        tyArr metaTy (tyArr (tyRecord metaRow) (tyRecord $ tyRowExtend l metaTy metaRow))
    TmMatch l -> do
      metaA <- TyVar <$> newMeta KindType
      metaB <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      pure . MetaT $
        tyArr (tyVariant $ tyRowExtend l metaA metaRow) $
        tyArr (tyArr metaA metaB) $
        tyArr (tyArr (tyVariant metaRow) metaB) $
        metaB
    TmInject l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      pure . MetaT $
        tyArr metaTy (tyVariant $ tyRowExtend l metaTy metaRow)
    TmEmbed l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      pure . MetaT $
        tyArr metaRow (tyVariant $ tyRowExtend l metaTy metaRow)

inferType
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar
     , Show tyVar
     )
  => Supply -- ^ Name supply
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (tyVar -> Maybe (Kind Void)) -- ^ Type variables
  -> (x -> Either tmVar (Ty tyVar)) -- ^ Term variables
  -> Tm tyVar x
  -> m (Forall tyVar)
inferType supply tyCtorCtx tyVarCtx varCtx tm =
  runEquivT
    id
    combineType
    (evalStateT
       (generalizeType =<<
        inferTypeM
          tyCtorCtx
          (fmap lift . varCtx)
          (first N tm))
       (InferState supply $ foldMeta (const Nothing) tyVarCtx))
