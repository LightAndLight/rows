{-# language DataKinds #-}
{-# language GADTs #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language UndecidableInstances #-}
module Inference.Type.Monad where

import Control.Applicative ((<|>))
import Control.Concurrent.Supply (freshId)
import Control.Lens.Fold (traverseOf_)
import Control.Lens.Getter (use, uses)
import Control.Lens.Plated (plate)
import Control.Lens.Setter ((%=), (.=))
import Control.Lens.Wrapped (_Unwrapped, _Wrapped)
import Control.Monad ((<=<))
import Control.Monad.Except (ExceptT, MonadError, runExceptT)
import Control.Monad.State (StateT, MonadState, evalStateT)
import Control.Monad.Trans.Class (lift)
import Data.Equivalence.Monad (EquivT, runEquivT, equate, classDesc)
import Data.IORef (newIORef, readIORef, writeIORef, modifyIORef')

import Inference.State
import Inference.Type.Error
import Kind
import Meta
import Ty

newtype TypeM s tyVar tmVar ev a
  = TypeM
  { unTypeM ::
      StateT
        (InferState Int tyVar ev)
        (EquivT s (MetaT 'Check Int Ty tyVar) (MetaT 'Check Int Ty tyVar)
           (ExceptT (TypeError Int tyVar tmVar) IO))
        a
  } deriving
  ( Functor, Applicative, Monad
  , MonadState (InferState Int tyVar ev)
  , MonadError (TypeError Int tyVar tmVar)
  )

displayType
  :: Traversable b
  => MetaT 'Check a b c
  -> TypeM s tyVar tmVar ev (DisplayMetaT a b c)
displayType = TypeM . lift . lift . lift . displayMetaT

showMetaT
  :: (Show a, forall x. Show x => Show (b x), Show c, Traversable b)
  => MetaT 'Check a b c
  -> TypeM s tyVar tmVar ev String
showMetaT = fmap show . displayType

eqMetaT
  :: (Eq a, forall x. Eq x => Eq (b x), Eq c, Traversable b)
  => MetaT 'Check a b c
  -> MetaT 'Check a b c
  -> TypeM s tyVar tmVar ev Bool
eqMetaT ma mb = (==) <$> displayType ma <*> displayType mb

combineType
  :: (Show a, Show b, Ord a, Eq b)
  => MetaT 'Check a Ty b
  -> MetaT 'Check a Ty b
  -> MetaT 'Check a Ty b
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
    go (TyVar (M _ _ a)) (TyVar (M n r b)) = TyVar $ M n r (min a b)
    go (TyApp a b) (TyApp a' b') = TyApp (go a a') (go b b')
    go (TyVar M{}) b = b
    go a (TyVar M{}) = a
    go _ _ = undefined

runTypeM
  :: forall tyVar tmVar ev a.
  (Show tyVar, Ord tyVar) =>
  InferState Int tyVar ev ->
  (forall s. TypeM s tyVar tmVar ev a) ->
  IO (Either (TypeError Int tyVar tmVar) a)
runTypeM is ma = runExceptT (runEquivT id combineType (go ma))
  where
    go ::
      forall s.
      TypeM s tyVar tmVar ev a ->
      EquivT s
        (MetaT 'Check Int Ty tyVar)
        (MetaT 'Check Int Ty tyVar)
        (ExceptT (TypeError Int tyVar tmVar) IO) a
    go (TypeM mb) = evalStateT mb is

equateType ::
  Ord tyVar =>
  MetaT 'Check Int Ty tyVar ->
  MetaT 'Check Int Ty tyVar ->
  TypeM s tyVar tmVar ev ()
equateType a b = go (unMetaT a) (unMetaT b)
  where
    -- when combining metas, we take the shallowest one, because we always
    -- want to know whether skolems will escape
    go (TyVar (M depth rank _)) (TyVar (M depth' rank' _)) = do
      TypeM . lift . lift . lift $ do
        d <- readIORef depth
        d' <- readIORef depth'
        let d'' = min d d'
        writeIORef depth $! d''
        writeIORef depth' $! d''

        r <- readIORef rank
        r' <- readIORef rank'
        let r'' = min r r'
        writeIORef rank $! r''
        writeIORef rank' $! r''

      TypeM . lift $ equate a b
    -- unifying a metavar with a type changes the ranks of all the
    -- metas in that type. If the meta was introduced into the context
    -- earlier (has a low rank), then the metas in the type are now
    -- considered to be "at least as early" as the meta
    go (TyVar (M depth rank _)) x = do
      TypeM . lift . lift . lift  $ do
        r <- readIORef rank
        d <- readIORef depth
        traverseOf_
          (traverse._M)
          (\(depth', rank', _) ->
            modifyIORef' depth' (min d) *>
            modifyIORef' rank' (min r))
          x
      TypeM . lift $ equate a b
    go x y@(TyVar M{}) = go y x
    go _ _ = TypeM . lift $ equate a b

findType ::
  Ord tyVar =>
  MetaT 'Check Int Ty tyVar ->
  TypeM s tyVar tmVar ev (MetaT 'Check Int Ty tyVar)
findType = TypeM . _Wrapped go
  where
    go = plate go <=< _Unwrapped (lift . classDesc)

newSkolem :: Kind Int -> TypeM s tyVar tmVar ev (Meta 'Check Int b)
newSkolem kind = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferKinds %=
    \f x ->
      f x <|>
      foldMeta
        (const Nothing)
        (\y -> if y == v then Just kind else Nothing)
        (const Nothing)
        x
  d <- use inferDepth
  depth <- TypeM . lift . lift . lift $ newIORef d
  pure $ S depth v

newMeta
  :: Rank
  -> Kind Int
  -> TypeM s tyVar tmVar ev (Meta 'Check Int b)
newMeta r kind = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferKinds %=
    \f x ->
      f x <|>
      foldMeta
        (\y -> if y == v then Just kind else Nothing)
        (const Nothing)
        (const Nothing)
        x
  d <- use inferDepth
  depth <- TypeM . lift . lift . lift $ newIORef d
  rank <- TypeM . lift . lift . lift $ newIORef r
  pure $ M depth rank v

newMetaInf :: Kind Int -> TypeM s tyVar tmVar ev (Meta 'Check Int b)
newMetaInf = newMeta Inf

newMetaRank :: Kind Int -> TypeM s tyVar tmVar ev (Meta 'Check Int b)
newMetaRank kind = flip newMeta kind . Rank =<< use inferRank

metaRank :: Meta 'Check a b -> TypeM s tyVar tmVar ev (Maybe Rank)
metaRank (M _ r _) = TypeM . lift . lift . lift $ Just <$> readIORef r
metaRank _ = pure Nothing

skolemDepth :: Meta 'Check a b -> TypeM s tyVar tmVar ev (Maybe Int)
skolemDepth (S d _) = TypeM . lift . lift . lift $ Just <$> readIORef d
skolemDepth _ = pure Nothing

metaDepth :: Meta 'Check a b -> TypeM s tyVar tmVar ev (Maybe Int)
metaDepth (M d _ _) = TypeM . lift . lift . lift $ Just <$> readIORef d
metaDepth _ = pure Nothing
