{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# language TemplateHaskell #-}
module Meta where

import Control.Lens.TH (makeWrapped, makePrisms)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Deriving (deriveEq1, deriveOrd1)
import Data.Functor.Classes (Eq1(..), Ord1(..), eq1, compare1)
import Data.IORef (IORef)

data Rank = Inf | Rank !Int deriving (Eq, Show)

instance Ord Rank where
  Inf <= Inf = True
  Inf <= Rank{} = False
  Rank{} <= Inf = True
  Rank a <= Rank b = a <= b

data Meta a b
  -- | Flexible meta variable
  = M { _metaDepth :: IORef Int, _metaRank :: IORef Rank, _metaValue :: a }
  -- | Rigid meta variable
  | S { _metaDepth :: IORef Int, _metaValue :: a }
  -- | Type variable
  | N b
  deriving (Functor, Foldable, Traversable)
makePrisms ''Meta

instance Eq a => Eq1 (Meta a) where
  liftEq _ (M _ _ v) (M _ _ v') = v == v'
  liftEq _ M{} S{} = False
  liftEq _ M{} N{} = False

  liftEq _ S{} M{} = False
  liftEq _ (S _ v) (S _ v') = v == v'
  liftEq _ S{} N{} = False

  liftEq _ N{} M{} = False
  liftEq _ N{} S{} = False
  liftEq f (N v) (N v') = f v v'

instance (Eq a, Eq b) => Eq (Meta a b) where
  (==) = eq1

instance Ord a => Ord1 (Meta a) where
  liftCompare _ (M _ _ v) (M _ _ v') = compare v v'
  liftCompare _ M{} S{} = LT
  liftCompare _ M{} N{} = LT

  liftCompare _ S{} M{} = GT
  liftCompare _ (S _ v) (S _ v') = compare v v'
  liftCompare _ S{} N{} = LT

  liftCompare _ N{} M{} = GT
  liftCompare _ N{} S{} = GT
  liftCompare f (N v) (N v') = f v v'

instance (Ord a, Ord b) => Ord (Meta a b) where
  compare = compare1

foldMeta :: (a -> r) -> (a -> r) -> (b -> r) -> Meta a b -> r
foldMeta f _ _ (M _ _ a) = f a
foldMeta _ g _ (S _ a) = g a
foldMeta _ _ h (N a) = h a

instance Applicative (Meta a) where
  pure = N
  N a <*> N b = N (a b)
  M n r a <*> _ = M n r a
  S n a <*> _ = S n a
  _ <*> M n r b = M n r b
  _ <*> S n b = S n b

instance Monad (Meta a) where
  N a >>= f = f a
  M n r a >>= _ = M n r a
  S n a >>= _ = S n a

newtype MetaT b m a = MetaT { unMetaT :: m (Meta b a) }
deriveEq1 ''MetaT
deriveOrd1 ''MetaT
makeWrapped ''MetaT

instance (Ord b, Ord a, Ord1 m) => Ord (MetaT b m a) where
  compare = compare1

instance (Eq b, Eq a, Eq1 m) => Eq (MetaT b m a) where
  (==) = eq1

instance Functor m => Functor (MetaT b m) where
  fmap f (MetaT m) = MetaT $ fmap (fmap f) m

instance Applicative m => Applicative (MetaT b m) where
  pure = MetaT . pure . pure
  MetaT a <*> MetaT b = MetaT $ (<*>) <$> a <*> b

instance Monad m => Monad (MetaT b m) where
  MetaT a >>= f =
    MetaT $ do
      a' <- a
      case a' of
        N x -> unMetaT $ f x
        M n r x -> pure $ M n r x
        S n x -> pure $ S n x

instance MonadTrans (MetaT b) where
  lift = MetaT . fmap N
