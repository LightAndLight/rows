{-# language DerivingVia #-}
{-# language LambdaCase #-}
module Eval where

import Control.Applicative ((<|>))
import Data.Monoid (Alt(..))

import Tm

newtype Step tyVar a
  = Step { runStep :: Tm tyVar a -> Maybe (Tm tyVar a) }
  deriving (Semigroup, Monoid) via (Tm tyVar a -> Alt Maybe (Tm tyVar a))

stepAdd :: Step tyVar a -> Step tyVar a
stepAdd step =
  Step $
  \case
    TmAdd (TmInt a) (TmInt b) -> Just $ TmInt (a + b)
    TmAdd a b ->
      TmAdd <$> runStep step a <*> pure b <|>
      TmAdd <$> pure a <*> runStep step b
    _ -> Nothing

runSteps :: [Step tyVar a -> Step tyVar a] -> Tm tyVar a -> Tm tyVar a
runSteps steps = go
  where
    go tm = maybe tm go $ runStep step tm
    step = foldMap ($ step) steps
