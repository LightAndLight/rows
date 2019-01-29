{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# language TemplateHaskell #-}
module Evidence where

import Control.Lens.TH (makeWrapped)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)
import Data.Functor.Classes (Eq1, Show1, Ord1, eq1, showsPrec1, compare1)

newtype Placeholder = Placeholder Int
  deriving (Eq, Show, Ord)

data Ev a = P Placeholder | V a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
deriveEq1 ''Ev
deriveOrd1 ''Ev
deriveShow1 ''Ev

foldEv :: (Placeholder -> r) -> (a -> r) -> Ev a -> r
foldEv f _ (P a) = f a
foldEv _ g (V a) = g a

instance Applicative Ev where
  pure = V
  V a <*> V b = V (a b)
  P a <*> _ = P a
  _ <*> P b = P b

instance Monad Ev where
  V a >>= f = f a
  P a >>= _ = P a

newtype EvT m a = EvT { unEvT :: m (Ev a) }
deriveEq1 ''EvT
deriveOrd1 ''EvT
deriveShow1 ''EvT
makeWrapped ''EvT

instance (Eq a, Eq1 m) => Eq (EvT m a) where
  (==) = eq1

instance (Show a, Show1 m) => Show (EvT m a) where
  showsPrec = showsPrec1

instance (Ord a, Ord1 m) => Ord (EvT m a) where
  compare = compare1

instance Functor m => Functor (EvT m) where
  fmap f (EvT m) = EvT $ fmap (fmap f) m

instance Foldable m => Foldable (EvT m) where
  foldMap f (EvT m) = foldMap (foldEv (const mempty) f) m

instance Applicative m => Applicative (EvT m) where
  pure = EvT . pure . pure
  EvT a <*> EvT b = EvT $ (<*>) <$> a <*> b

instance Monad m => Monad (EvT m) where
  EvT a >>= f =
    EvT $ do
      a' <- a
      case a' of
        V x -> unEvT $ f x
        P x -> pure $ P x

instance MonadTrans EvT where
  lift = EvT . fmap V
