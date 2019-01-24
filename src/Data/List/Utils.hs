module Data.List.Utils where

import Data.Monoid (Any(..), Ap(..))

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

filterM :: (Monad m, Foldable t) => (a -> m Bool) -> t a -> m [a]
filterM p = foldr (\a b -> p a >>= \x -> if x then (a :) <$> b else b) (pure [])