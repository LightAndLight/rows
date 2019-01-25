module Bound.Scope.Utils where

import Bound.Scope (Scope(..))
import Bound.Var (Var(..), unvar)

applyVars ::
  Monad f =>
  Int -> -- ^ Number of variables to apply (must be less than the number of variables bound in the scope)
  [a] -> -- ^ Variables to apply
  Scope Int f a ->
  Scope Int f a
applyVars n vs =
  Scope .
  fmap (unvar (\b -> if b >= n then B (b - n) else F (pure $ vs !! b)) F) .
  unscope
