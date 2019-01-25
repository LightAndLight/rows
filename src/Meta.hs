{-# language DataKinds, TypeFamilies, KindSignatures #-}
{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}
{-# language FunctionalDependencies #-}
{-# language QuantifiedConstraints #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Meta where

import Control.Lens.TH (makeWrapped, makeClassyPrisms)
import Control.Lens.Wrapped (_Wrapped)
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Deriving (deriveEq1, deriveOrd1)
import Data.Functor.Classes (Eq1(..), Ord1(..), eq1, compare1)
import Data.IORef (IORef, readIORef)

data Rank = Inf | Rank !Int deriving (Eq, Show)

instance Ord Rank where
  Inf <= Inf = True
  Inf <= Rank{} = False
  Rank{} <= Inf = True
  Rank a <= Rank b = a <= b

data MetaStage = Check | Display
type family MetaCell (m :: MetaStage) (x :: *) where
  MetaCell 'Display x = x
  MetaCell 'Check x = IORef x

data Meta (s :: MetaStage) a b
  -- | Flexible meta variable
  = M { _metaDepth :: MetaCell s Int, _metaRank :: MetaCell s Rank, _metaValue :: a }
  -- | Rigid meta variable
  | S { _metaDepth :: MetaCell s Int, _metaValue :: a }
  -- | Type variable
  | N b
  deriving (Functor, Foldable, Traversable)
makeClassyPrisms ''Meta

deriving instance (Show a, Show b) => Show (Meta 'Display a b)

newtype DisplayMeta a b = DisplayMeta (Meta 'Display a b)
  deriving Show
makeWrapped ''DisplayMeta

instance AsMeta (DisplayMeta a b) 'Display a b where
  _Meta = _Wrapped

instance (Eq a, Eq b) => Eq (DisplayMeta a b) where
  DisplayMeta a == DisplayMeta b =
    case (a, b) of
      (M x y z, M x' y' z') -> x == x' && y == y' && z == z'
      (S x y, S x' y') -> x == x' && y == y'
      (N x, N x') -> x == x'
      _ -> False

instance (Ord a, Ord b) => Ord (DisplayMeta a b) where
  DisplayMeta a `compare` DisplayMeta b =
    case (a, b) of
      (M x y z, M x' y' z') ->
        case compare x x' of
          EQ ->
            case compare y y' of
              EQ -> compare z z'
              y'' -> y''
          x'' -> x''
      (M{}, S{}) -> LT
      (M{}, N{}) -> LT

      (S{}, M{}) -> GT
      (S x y, S x' y') ->
        case compare x x' of
          EQ -> compare y y'
          x'' -> x''
      (S{}, N{}) -> LT

      (N{}, M{}) -> GT
      (N{}, S{}) -> GT
      (N x, N x') -> compare x x'

displayMeta :: Meta 'Check a b -> IO (DisplayMeta a b)
displayMeta m =
  DisplayMeta <$>
  case m of
    M a b c -> do
      a' <- readIORef a
      b' <- readIORef b
      pure $ M a' b' c
    S a b -> do
      a' <- readIORef a
      pure $ S a' b
    N a -> pure $ N a

instance Eq a => Eq1 (Meta s a) where
  liftEq _ (M _ _ v) (M _ _ v') = v == v'
  liftEq _ M{} S{} = False
  liftEq _ M{} N{} = False

  liftEq _ S{} M{} = False
  liftEq _ (S _ v) (S _ v') = v == v'
  liftEq _ S{} N{} = False

  liftEq _ N{} M{} = False
  liftEq _ N{} S{} = False
  liftEq f (N v) (N v') = f v v'

instance (Eq a, Eq b) => Eq (Meta s a b) where
  (==) = eq1

instance Ord a => Ord1 (Meta s a) where
  liftCompare _ (M _ _ v) (M _ _ v') = compare v v'
  liftCompare _ M{} S{} = LT
  liftCompare _ M{} N{} = LT

  liftCompare _ S{} M{} = GT
  liftCompare _ (S _ v) (S _ v') = compare v v'
  liftCompare _ S{} N{} = LT

  liftCompare _ N{} M{} = GT
  liftCompare _ N{} S{} = GT
  liftCompare f (N v) (N v') = f v v'

instance (Ord a, Ord b) => Ord (Meta s a b) where
  compare = compare1

foldMeta :: (a -> r) -> (a -> r) -> (b -> r) -> Meta s a b -> r
foldMeta f _ _ (M _ _ a) = f a
foldMeta _ g _ (S _ a) = g a
foldMeta _ _ h (N a) = h a

instance Applicative (Meta s a) where
  pure = N
  N a <*> N b = N (a b)
  M n r a <*> _ = M n r a
  S n a <*> _ = S n a
  _ <*> M n r b = M n r b
  _ <*> S n b = S n b

instance Monad (Meta s a) where
  N a >>= f = f a
  M n r a >>= _ = M n r a
  S n a >>= _ = S n a

newtype MetaT s b m a = MetaT { unMetaT :: m (Meta s b a) }
deriveEq1 ''MetaT
deriveOrd1 ''MetaT
makeWrapped ''MetaT

deriving instance
  ( Show a
  , Show b
  , forall x. Show x => (Show (m x))
  ) => Show (MetaT 'Display a m b)

newtype DisplayMetaT b m a = DisplayMetaT (m (DisplayMeta b a))

deriving instance
  (Eq a, Eq b, forall x. Eq x => Eq (m x)) => Eq (DisplayMetaT a m b)

deriving instance
  (Show a, Show b, forall x. Show x => Show (m x)) => Show (DisplayMetaT a m b)

displayMetaT ::
  Traversable m =>
  MetaT 'Check a m b ->
  IO (DisplayMetaT a m b)
displayMetaT (MetaT s) = DisplayMetaT <$> traverse displayMeta s

instance (Ord b, Ord a, Ord1 m) => Ord (MetaT s b m a) where
  compare = compare1

instance (Eq b, Eq a, Eq1 m) => Eq (MetaT s b m a) where
  (==) = eq1

instance Functor m => Functor (MetaT s b m) where
  fmap f (MetaT m) = MetaT $ fmap (fmap f) m

instance Applicative m => Applicative (MetaT s b m) where
  pure = MetaT . pure . pure
  MetaT a <*> MetaT b = MetaT $ (<*>) <$> a <*> b

instance Monad m => Monad (MetaT s b m) where
  MetaT a >>= f =
    MetaT $ do
      a' <- a
      case a' of
        N x -> unMetaT $ f x
        M n r x -> pure $ M n r x
        S n x -> pure $ S n x

instance MonadTrans (MetaT s b) where
  lift = MetaT . fmap N

instance MonadTrans (DisplayMetaT b) where
  lift = DisplayMetaT . fmap (DisplayMeta . N)

liftDM :: Applicative m => Meta 'Display a b -> DisplayMetaT a m b
liftDM = DisplayMetaT . pure . DisplayMeta