{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language UndecidableInstances #-}
module Inference.Type.Monad where

import Control.Lens.Plated (plate)
import Control.Lens.Wrapped (_Unwrapped, _Wrapped)
import Control.Monad ((<=<))
import Control.Monad.Except (MonadError)
import Control.Monad.State (StateT, MonadState, evalStateT)
import Control.Monad.Trans.Class (MonadTrans, lift)
import Data.Equivalence.Monad (EquivT, runEquivT, equate, classDesc)

import Inference.State
import Meta
import Ty

newtype TypeM s tyVar ev m a
  = TypeM
  { unTypeM ::
      StateT
        (InferState Int tyVar ev)
        (EquivT s (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m) a
  } deriving
  ( Functor, Applicative, Monad
  , MonadState (InferState Int tyVar ev)
  )
deriving instance MonadError e m => MonadError e (TypeM s tyVar ev m)
instance MonadTrans (TypeM s tyVar ev) where
  lift = TypeM . lift . lift

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
    go TyInt TyInt = TyInt
    go (TyRowExtend l) (TyRowExtend l') | l == l' = TyRowExtend l
    go (TyCtor s) (TyCtor s') | s == s' = TyCtor s
    -- if two skolems are equal then they necessarily have the same depth
    go (TyVar (S _ a)) (TyVar (S d b)) | a == b = TyVar (S d b)
    go (TyVar (N a)) (TyVar (N b)) | a == b = TyVar (N b)
    -- when combining metas, we take the shallowest one, because we always
    -- want to know whether skolems will escape
    go (TyVar (M n a)) (TyVar (M n' b)) = TyVar $ M (min n n') (min a b)
    go (TyApp a b) (TyApp a' b') = TyApp (go a a') (go b b')
    go (TyVar M{}) b = b
    go a (TyVar M{}) = a
    go _ _ =
      error $
      "combineType: combining un-unifiable terms\n\n" <>
      show x <>
      "\n\n" <>
      show y

runTypeM ::
  forall tyVar ev m a.
  (Monad m, Show tyVar, Ord tyVar) =>
  InferState Int tyVar ev ->
  (forall s. TypeM s tyVar ev m a) ->
  m a
runTypeM is ma = runEquivT id combineType (go ma)
  where
    go ::
      forall s.
      TypeM s tyVar ev m a ->
      EquivT s (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m a
    go (TypeM mb) = evalStateT mb is

equateType ::
  (Monad m, Ord tyVar) =>
  MetaT Int Ty tyVar ->
  MetaT Int Ty tyVar ->
  TypeM s tyVar ev m ()
equateType a b = TypeM $ lift $ equate a b

findType :: (Monad m, Ord tyVar) => MetaT Int Ty tyVar -> TypeM s tyVar ev m (MetaT Int Ty tyVar)
findType = TypeM . _Wrapped go
  where
    go = plate go <=< _Unwrapped (lift . classDesc)
