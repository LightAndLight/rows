module Data.List.Utils where

import Data.Monoid (Any(..), All(..), Ap(..))

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM p xs = foldr select (pure ([], [])) xs
  where
    select x acc = do
      res <- p x
      ~(ts, fs) <- acc
      if res
        then pure (x:ts, fs)
        else pure (ts, x:fs)

anyA :: (Applicative f, Foldable t) => (a -> f Bool) -> t a -> f Bool
anyA f = fmap getAny . getAp . foldMap (Ap . fmap Any . f)

allA :: (Applicative f, Foldable t) => (a -> f Bool) -> t a -> f Bool
allA f = fmap getAll . getAp . foldMap (Ap . fmap All . f)

filterM :: (Monad m, Foldable t) => (a -> m Bool) -> t a -> m [a]
filterM p = foldr (\a b -> p a >>= \x -> if x then (a :) <$> b else b) (pure [])

findM :: (Monad m, Foldable f) => (a -> m Bool) -> f a -> m (Maybe a)
findM p =
  foldr
    (\a b -> p a >>= \x -> if x then pure (Just a) else b)
    (pure Nothing)