{-# language FlexibleContexts #-}
{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
module Inference.Kind where

import Control.Applicative ((<|>))
import Control.Concurrent.Supply (Supply, freshId)
import Control.Lens.Review ((#))
import Control.Lens.TH (makeClassyPrisms)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, state)
import Data.Equivalence.Monad (MonadEquiv, EquivT, equate, classDesc, runEquivT)
import Data.Foldable (for_)
import Data.Traversable (for)
import Data.Void (Void, absurd)

import Kind
import Ty

data KindError a
  = KindOccurs Int (Kind Int)
  | KindMismatch (Kind Int) (Kind Int)
  | KindVarNotFound a
  | KindCtorNotFound String
  deriving (Eq, Show)
makeClassyPrisms ''KindError

occursKind :: Eq meta => meta -> Kind meta -> Bool
occursKind v = foldr (\a b -> a == v || b) False

combineKind :: Kind Int -> Kind Int -> Kind Int
combineKind KindType KindType = KindType
combineKind KindRow KindRow = KindRow
combineKind (KindArr x y) (KindArr x' y') =
  KindArr (combineKind x x') (combineKind y y')
combineKind (KindVar x) (KindVar y) = KindVar (min x y)
combineKind KindVar{} y = y
combineKind x KindVar{} = x
combineKind _ _ = error "combineKind: combining un-unifiable terms"

zonkKinds
  :: MonadEquiv c (Kind Int) (Kind Int) m
  => Kind Int
  -> m (Kind Void)
zonkKinds k =
  case k of
    KindVar v -> do
      k' <- classDesc $ KindVar v
      case k' of
        KindVar v' | v == v' -> pure KindType
        _ -> zonkKinds k'
    KindType -> pure KindType
    KindRow -> pure KindRow
    KindArr x y -> KindArr <$> zonkKinds x <*> zonkKinds y

unifyKind
  :: ( AsKindError e a
     , MonadError e m
     , MonadEquiv c (Kind Int) (Kind Int) m
     )
  => Kind Int
  -> Kind Int
  -> m ()
unifyKind (KindVar x) (KindVar y) = equate (KindVar x) (KindVar y)
unifyKind (KindVar x) k =
  if occursKind x k
  then throwError $ _KindOccurs # (x, k)
  else equate (KindVar x) k
unifyKind k (KindVar x) =
  if occursKind x k
  then throwError $ _KindOccurs # (x, k)
  else equate (KindVar x) k
unifyKind KindType KindType = pure ()
unifyKind KindRow KindRow = pure ()
unifyKind (KindArr x y) (KindArr x' y') = unifyKind x x' *> unifyKind y y'
unifyKind x y = throwError $ _KindMismatch # (x, y)

inferKindM
  :: ( MonadState Supply m
     , AsKindError e a
     , MonadError e m
     , MonadEquiv c (Kind Int) (Kind Int) m
     )
  => (String -> Maybe (Kind Int))
  -> (a -> Maybe (Kind Int))
  -> Ty a
  -> m (Kind Int)
inferKindM _ _ TyArr = pure $ KindArr KindType (KindArr KindType KindType)
inferKindM ctorCtx _ (TyCtor s) =
  maybe (throwError $ _KindCtorNotFound # s) pure $ ctorCtx s
inferKindM _ varCtx (TyVar x) =
  maybe (throwError $ _KindVarNotFound # x) pure $ varCtx x
inferKindM ctorCtx varCtx (TyApp x y) = do
  xKind <- inferKindM ctorCtx varCtx x
  yKind <- inferKindM ctorCtx varCtx y
  retKind <- KindVar <$> state freshId
  unifyKind xKind (KindArr yKind retKind)
  pure retKind

inferDataDeclKind
  :: forall e a m
   . ( MonadState Supply m
     , AsKindError e a
     , MonadError e m
     , Eq a
     )
  => (String -> Maybe (Kind Void)) -- ^ Constructors
  -> (a -> Maybe (Kind Void)) -- ^ Variables
  -> (String, [a]) -- ^ Type constructor and arguments
  -> [[Ty a]] -- ^ Fields for each data constructor
  -> m (Kind Void)
inferDataDeclKind ctorCtx varCtx (ctor, params) branches =
  runEquivT id combineKind go
  where
    go :: forall s. EquivT s (Kind Int) (Kind Int) m (Kind Void)
    go = do
      paramKinds <- for params $ \p -> (p,) . KindVar <$> state freshId
      let ctorKind = foldr (KindArr . snd) KindType paramKinds

      let
        ctorCtx' x =
          fmap (fmap absurd) (ctorCtx x) <|>
          (if x == ctor then Just ctorKind else Nothing)

      let
        varCtx' x =
          fmap (fmap absurd) (varCtx x) <|>
          lookup x paramKinds

      for_ branches $ \branch ->
        for_ branch $ \ty -> do
          k <- inferKindM ctorCtx' varCtx' ty
          unifyKind k KindType

      zonkKinds ctorKind

inferKind
  :: forall e a m
   . ( MonadState Supply m
     , AsKindError e a
     , MonadError e m
     )
  => (String -> Maybe (Kind Void)) -- ^ Constructors
  -> (a -> Maybe (Kind Void)) -- ^ Variables
  -> Ty a
  -> m (Kind Void)
inferKind a b ty =
  runEquivT
    id
    combineKind
    (zonkKinds =<<
     inferKindM (fmap (fmap absurd) . a) (fmap (fmap absurd) . b) ty)
