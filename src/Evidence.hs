{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# language TemplateHaskell #-}
module Evidence where

import Control.Lens.TH (makeWrapped)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)
import Data.Functor.Classes (Eq1, Show1, Ord1, eq1, showsPrec1, compare1)

data Ev a b = E a | V b
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
deriveEq1 ''Ev
deriveOrd1 ''Ev
deriveShow1 ''Ev

foldEv :: (a -> r) -> (b -> r) -> Ev a b -> r
foldEv f _ (E a) = f a
foldEv _ g (V a) = g a

instance Applicative (Ev a) where
  pure = V
  V a <*> V b = V (a b)
  E a <*> _ = E a
  _ <*> E b = E b

instance Monad (Ev a) where
  V a >>= f = f a
  E a >>= _ = E a

newtype EvT b m a = EvT { unEvT :: m (Ev b a) }
deriveEq1 ''EvT
deriveOrd1 ''EvT
deriveShow1 ''EvT
makeWrapped ''EvT

instance (Eq b, Eq a, Eq1 m) => Eq (EvT b m a) where
  (==) = eq1

instance (Show b, Show a, Show1 m) => Show (EvT b m a) where
  showsPrec = showsPrec1

instance (Ord b, Ord a, Ord1 m) => Ord (EvT b m a) where
  compare = compare1

instance Functor m => Functor (EvT b m) where
  fmap f (EvT m) = EvT $ fmap (fmap f) m

instance Foldable m => Foldable (EvT b m) where
  foldMap f (EvT m) = foldMap (foldEv (const mempty) f) m

instance Applicative m => Applicative (EvT b m) where
  pure = EvT . pure . pure
  EvT a <*> EvT b = EvT $ (<*>) <$> a <*> b

instance Monad m => Monad (EvT b m) where
  EvT a >>= f =
    EvT $ do
      a' <- a
      case a' of
        V x -> unEvT $ f x
        E x -> pure $ E x

instance MonadTrans (EvT b) where
  lift = EvT . fmap V
