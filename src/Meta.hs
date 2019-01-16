{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module Meta where

import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)
import Data.Functor.Classes (Eq1, Show1, Ord1, eq1, showsPrec1, compare1)

data Meta a b = M a | N b
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
deriveEq1 ''Meta
deriveOrd1 ''Meta
deriveShow1 ''Meta

foldMeta :: (a -> r) -> (b -> r) -> Meta a b -> r
foldMeta f _ (M a) = f a
foldMeta _ g (N a) = g a

instance Applicative (Meta a) where
  pure = N
  N a <*> N b = N (a b)
  M a <*> _ = M a
  _ <*> M b = M b

instance Monad (Meta a) where
  N a >>= f = f a
  M a >>= _ = M a

newtype MetaT b m a = MetaT { unMetaT :: m (Meta b a) }
deriveEq1 ''MetaT
deriveOrd1 ''MetaT
deriveShow1 ''MetaT

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
        M x -> pure $ M x

instance MonadTrans (MetaT b) where
  lift = MetaT . fmap N

meta :: Applicative m => b -> MetaT b m a
meta = MetaT . pure . M