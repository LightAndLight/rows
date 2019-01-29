{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving, UndecidableInstances #-}
{-# language TupleSections #-}
module Inference.Kind where

import Bound.Scope (fromScope)
import Bound.Var (unvar)
import Control.Applicative ((<|>))
import Control.Concurrent.Supply (Supply, freshId)
import Control.Lens.Plated (plate)
import Control.Lens.Review ((#))
import Control.Lens.Traversal (traverseOf)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Trans.Class (MonadTrans, lift)
import Control.Monad.State (MonadState(..), StateT, evalStateT, state)
import Data.Equivalence.Monad (EquivT, equate, classDesc, runEquivT)
import Data.Foldable (for_)
import Data.Traversable (for)
import Data.Void (Void, absurd)

import Inference.Kind.Error
import Kind
import Ty

newtype KindM s m a
  = KindM
  { unKindM :: StateT Supply (EquivT s (Kind Int) (Kind Int) m) a
  } deriving (Functor, Applicative, Monad)
deriving instance MonadError e m => MonadError e (KindM s m)

instance MonadState s m => MonadState s (KindM s' m) where
  get = lift get
  put = lift . put

instance MonadTrans (KindM s) where
  lift = KindM . lift . lift

combineKind :: Kind Int -> Kind Int -> Kind Int
combineKind KindType KindType = KindType
combineKind KindRow KindRow = KindRow
combineKind (KindArr x y) (KindArr x' y') =
  KindArr (combineKind x x') (combineKind y y')
combineKind (KindVar x) (KindVar y) = KindVar (min x y)
combineKind KindVar{} y = y
combineKind x KindVar{} = x
combineKind _ _ = error "combineKind: combining un-unifiable terms"

runKindM :: forall m a. Monad m => Supply -> (forall s. KindM s m a) -> m a
runKindM supply ma = runEquivT id combineKind (go ma)
  where
    go :: forall s. KindM s m a -> EquivT s (Kind Int) (Kind Int) m a
    go (KindM mb) = evalStateT mb supply

equateKind :: Monad m => Kind Int -> Kind Int -> KindM s m ()
equateKind a b = KindM $ lift $ equate a b

newKindMeta :: Monad m => KindM s m Int
newKindMeta = KindM $ state freshId

findKind :: Monad m => Kind Int -> KindM s m (Kind Int)
findKind a = KindM $ go a
  where
    go b = traverseOf plate go =<< lift (classDesc b)

occursKind :: Eq meta => meta -> Kind meta -> Bool
occursKind v = foldr (\a b -> a == v || b) False

zonkKinds :: Monad m => Kind Int -> KindM s m (Kind Void)
zonkKinds k = (>> KindType) <$> findKind k

unifyKind
  :: ( AsKindError e a
     , MonadError e m
     )
  => Kind Int
  -> Kind Int
  -> KindM s m ()
unifyKind x y = do
  x' <- findKind x
  y' <- findKind y
  go x' y'
  where
    go (KindVar x') (KindVar y') = equateKind (KindVar x') (KindVar y')
    go (KindVar x') k =
      if occursKind x' k
      then throwError $ _KindOccurs # (x', k)
      else equateKind (KindVar x') k
    go k (KindVar x') =
      if occursKind x' k
      then throwError $ _KindOccurs # (x', k)
      else equateKind (KindVar x') k
    go KindType KindType = pure ()
    go KindRow KindRow = pure ()
    go KindConstraint KindConstraint = pure ()
    go (KindArr x' y') (KindArr x'' y'') =
      unifyKind x' x'' *>
      unifyKind y' y''
    go x' y' = throwError $ _KindMismatch # (x', y')

unsafeKindMap :: (Eq a, Show a) => [(a, b)] -> (a -> Either x b)
unsafeKindMap mp x =
  maybe (error $ show x <> " not in kind map") Right $
  lookup x mp

inferKindM
  :: ( AsKindError e a
     , MonadError e m
     )
  => (String -> Maybe (Kind Int))
  -> (x -> m (Either a (Kind Int)))
  -> Ty x
  -> KindM s m (Kind Int)
inferKindM ctorCtx varCtx (TyForall n s) = do
  metas <- for [0..n-1] $ \x -> (,) x . KindVar <$> newKindMeta
  k <-
    inferKindM
      ctorCtx
      (unvar (pure . unsafeKindMap metas) varCtx)
      (fromScope s)
  unifyKind k KindType
  pure KindType
inferKindM ctorCtx varCtx (TyExists n s) = do
  metas <- for [0..n-1] $ \x -> (,) x . KindVar <$> newKindMeta
  k <-
    inferKindM
      ctorCtx
      (unvar (pure . unsafeKindMap metas) varCtx)
      (fromScope s)
  unifyKind k KindType
  pure KindType
inferKindM _ _ TyArr = pure $ KindArr KindType (KindArr KindType KindType)
inferKindM _ _ TyConstraint =
  pure $ KindArr KindConstraint (KindArr KindType KindType)
inferKindM ctorCtx _ (TyCtor s) =
  maybe (throwError $ _KindCtorNotFound # s) pure $ ctorCtx s
inferKindM _ varCtx (TyVar x) =
  lift (varCtx x) >>=
  either (throwError . (_KindVarNotFound #)) pure
inferKindM ctorCtx varCtx (TyApp x y) = do
  xKind <- inferKindM ctorCtx varCtx x
  yKind <- inferKindM ctorCtx varCtx y
  retKind <- KindVar <$> newKindMeta
  unifyKind xKind (KindArr yKind retKind)
  pure retKind
inferKindM _ _ TyRowEmpty =
  pure KindRow
inferKindM _ _ TyRecord =
  pure $ KindArr KindRow KindType
inferKindM _ _ TyVariant =
  pure $ KindArr KindRow KindType
inferKindM _ _ TyRowExtend{} =
  pure $ KindArr KindType (KindArr KindRow KindRow)
inferKindM _ _ TyOffset{} =
  pure $ KindArr KindRow KindConstraint
inferKindM _ _ TyInt{} =
  pure KindType

inferDataDeclKind
  :: forall x e a m
   . ( AsKindError e a
     , MonadError e m
     , Eq x
     )
  => Supply -- ^ Variable supply
  -> (x -> m a) -- ^ Freeze variables
  -> (String -> Maybe (Kind Void)) -- ^ Constructors
  -> (x -> Maybe (Kind Void)) -- ^ Variables
  -> (String, [x]) -- ^ Type constructor and arguments
  -> [[Ty x]] -- ^ Fields for each data constructor
  -> m (Kind Void)
inferDataDeclKind supply freezeVars ctorCtx varCtx (ctor, params) branches =
  runKindM supply go
  where
    go :: forall s. KindM s m (Kind Void)
    go = do
      paramKinds <- for params $ \p -> (p,) . KindVar <$> newKindMeta
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
          k <-
            inferKindM
              ctorCtx'
              (\x -> maybe (Left <$> freezeVars x) (pure . Right) $ varCtx' x)
              ty
          unifyKind k KindType

      zonkKinds ctorKind

inferKind
  :: forall x e a m
   . ( AsKindError e a
     , MonadError e m
     )
  => Supply -- ^ Variable supply
  -> (x -> m a) -- ^ Freeze variables
  -> (String -> Maybe (Kind Void)) -- ^ Constructors
  -> (x -> Maybe (Kind Void)) -- ^ Variables
  -> Ty x
  -> m (Kind Void)
inferKind supply freezeVars a b ty =
  runKindM
    supply
    (zonkKinds =<<
     inferKindM
       (fmap (fmap absurd) . a)
       (\x -> maybe (Left <$> freezeVars x) (pure . Right) . fmap (fmap absurd) $ b x)
       ty)
