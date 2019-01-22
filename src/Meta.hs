{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# language TemplateHaskell #-}
module Meta where

import Control.Lens.TH (makeWrapped)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)
import Data.Functor.Classes (Eq1, Show1, Ord1, eq1, showsPrec1, compare1)

data Meta a b
  -- | Flexible meta variable
  = M { _metaDepth :: Int, _metaValue :: a }
  -- | Rigid meta variable
  | S { _metaDepth :: Int, _metaValue :: a }
  -- | Type variable
  | N b
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
deriveEq1 ''Meta
deriveOrd1 ''Meta
deriveShow1 ''Meta

foldMeta :: (Int -> a -> r) -> (Int -> a -> r) -> (b -> r) -> Meta a b -> r
foldMeta f _ _ (M n a) = f n a
foldMeta _ g _ (S n a) = g n a
foldMeta _ _ h (N a) = h a

instance Applicative (Meta a) where
  pure = N
  N a <*> N b = N (a b)
  M n a <*> _ = M n a
  S n a <*> _ = S n a
  _ <*> M n b = M n b
  _ <*> S n b = S n b

instance Monad (Meta a) where
  N a >>= f = f a
  M n a >>= _ = M n a
  S n a >>= _ = S n a

newtype MetaT b m a = MetaT { unMetaT :: m (Meta b a) }
deriveEq1 ''MetaT
deriveOrd1 ''MetaT
deriveShow1 ''MetaT
makeWrapped ''MetaT

instance (Eq b, Eq a, Eq1 m) => Eq (MetaT b m a) where
  (==) = eq1

instance (Show b, Show a, Show1 m) => Show (MetaT b m a) where
  showsPrec = showsPrec1

instance (Ord b, Ord a, Ord1 m) => Ord (MetaT b m a) where
  compare = compare1

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
        M n x -> pure $ M n x
        S n x -> pure $ S n x

instance MonadTrans (MetaT b) where
  lift = MetaT . fmap N

meta :: Applicative m => Int -> b -> MetaT b m a
meta n = MetaT . pure . M n

skolem :: Applicative m => Int -> b -> MetaT b m a
skolem n = MetaT . pure . S n
