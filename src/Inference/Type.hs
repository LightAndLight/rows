{-# language FlexibleContexts #-}
{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Inference.Type where

import Bound.Scope (abstractEither, fromScope)
import Bound.Var (unvar)
import Control.Applicative ((<|>))
import Control.Concurrent.Supply (Supply, freshId)
import Control.Lens.TH (makeClassyPrisms)
import Control.Lens.Review ((#))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, state)
import Control.Monad.Trans.Class (lift)
import Data.Equivalence.Monad (MonadEquiv, equate, classDesc, runEquivT)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.Void (Void, absurd)

import qualified Data.Set as Set

import Kind
import Inference.Kind
import Meta
import Tm
import Ty

data TypeError a b c
  = TypeOccurs a (MetaT a Ty b)
  | TypeMismatch (MetaT a Ty b) (MetaT a Ty b)
  | TypeVarNotFound c
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

combineType :: (Ord a, Eq b) => MetaT a Ty b -> MetaT a Ty b -> MetaT a Ty b
combineType (MetaT x) (MetaT y) = MetaT $ go x y
  where
    go TyArr TyArr = TyArr
    go (TyCtor s) (TyCtor s') | s == s' = TyCtor s
    go (TyVar (N a)) (TyVar (N b)) | a == b = TyVar (N b)
    go (TyVar (M a)) (TyVar (M b)) = TyVar $ M (min a b)
    go (TyApp a b) (TyApp a' b') = TyApp (go a a') (go b b')
    go (TyVar M{}) b = b
    go a (TyVar M{}) = a
    go _ _ = error "combineType: combining un-unifiable terms"

unifyType
  :: forall tmVar tyVar c m
   . ( MonadError (TypeError Int tyVar tmVar) m
     , MonadState Supply m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar
     )
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (Meta Int tyVar -> Maybe (Kind Void)) -- ^ Type variables
  -> MetaT Int Ty tyVar
  -> MetaT Int Ty tyVar
  -> m ()
unifyType tyCtorCtx tyVarCtx (MetaT x) (MetaT y) = do
  xKind <- inferKind tyCtorCtx tyVarCtx x
  yKind <- inferKind tyCtorCtx tyVarCtx y
  if xKind == yKind
    then go x y
    else throwError $ _KindMismatch # (absurd <$> xKind, absurd <$> yKind)
  where
    go :: Ty (Meta Int tyVar) -> Ty (Meta Int tyVar) -> m ()
    go TyArr TyArr = pure ()
    go (TyCtor s) (TyCtor s') | s == s' = pure ()
    go (TyVar (N a)) (TyVar (N b)) | a == b = pure ()
    go (TyVar M{}) (TyVar M{}) = equate (MetaT x) (MetaT y)
    go (TyApp a b) (TyApp a' b') =
      unifyType tyCtorCtx tyVarCtx (MetaT a) (MetaT a') *>
      unifyType tyCtorCtx tyVarCtx (MetaT b) (MetaT b')
    go (TyVar (M a)) ty =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else equate (MetaT x) (MetaT y)
    go ty (TyVar (M a)) =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else equate (MetaT x) (MetaT y)
    go _ _ = throwError $ TypeMismatch (MetaT x) (MetaT y)

generalizeType
  :: forall tyVar tmVar c m
   . ( MonadState Supply m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar
     )
  => MetaT Int Ty tyVar
  -> m (Forall tyVar)
generalizeType = fmap generalize . find
  where
    find :: MetaT Int Ty tyVar -> m (Ty (Meta Int tyVar))
    find (MetaT ty) =
      case ty of
        TyArr -> pure TyArr
        TyCtor s -> pure $ TyCtor s
        TyVar (N a) -> pure $ TyVar (N a)
        TyVar (M a) -> do
          ty' <- unMetaT <$> classDesc (MetaT ty)
          case ty' of
            TyVar (M a') | a == a' -> pure ty'
            _ -> find $ MetaT ty'
        TyApp a b -> TyApp <$> find (MetaT a) <*> find (MetaT b)

    generalize :: Ty (Meta Int tyVar) -> Forall tyVar
    generalize t =
      Forall (length metas) $
      abstractEither (foldMeta (Left . fromJust . (`elemIndex` metas)) Right) t
      where
        metas :: [Int]
        metas =
          Set.toList $
          foldr
            (\a b -> foldMeta (`Set.insert` b) (const b) a)
            Set.empty
            t

inferTypeM
  :: ( MonadState Supply m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar
     )
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (Meta Int tyVar -> Maybe (Kind Void)) -- ^ Type variables
  -> (x -> Either tmVar (MetaT Int Ty tyVar))
  -> Tm x
  -> m (MetaT Int Ty tyVar)
inferTypeM tyCtorCtx tyVarCtx varCtx tm =
  case tm of
    TmVar a ->
      either (throwError . TypeVarNotFound) pure $ varCtx a
    TmApp a b -> do
      aTy <- inferTypeM tyCtorCtx tyVarCtx varCtx a
      bTy <- unMetaT <$> inferTypeM tyCtorCtx tyVarCtx varCtx b
      retTy <- M <$> state freshId
      unifyType
        tyCtorCtx
        (\x -> tyVarCtx x <|> if x == retTy then Just KindType else Nothing)
        aTy (MetaT $ TyApp (TyApp TyArr bTy) (TyVar retTy))
      pure $ MetaT $ TyVar retTy
    TmLam s -> do
      argTy <- M <$> state freshId
      bodyTy <-
        inferTypeM
          tyCtorCtx
          (\x -> tyVarCtx x <|> if x == argTy then Just KindType else Nothing)
          (unvar (const $ Right $ MetaT $ TyVar argTy) varCtx)
          (fromScope s)
      pure . MetaT $ TyApp (TyApp TyArr (TyVar argTy)) (unMetaT bodyTy)

inferType
  :: ( MonadState Supply m
     , MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar
     )
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (tyVar -> Maybe (Kind Void)) -- ^ Type variables
  -> (x -> Either tmVar (Ty tyVar)) -- ^ Term variables
  -> Tm x
  -> m (Forall tyVar)
inferType tyCtorCtx tyVarCtx varCtx tm =
  runEquivT
    id
    combineType
    (generalizeType =<<
     inferTypeM
       tyCtorCtx
       (foldMeta (const Nothing) tyVarCtx)
       (fmap lift . varCtx)
       tm)
