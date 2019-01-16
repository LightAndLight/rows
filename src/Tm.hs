{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Tm where

import Bound.Scope (Scope, abstract1)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)

data Tm a
  = TmVar a
  | TmApp (Tm a) (Tm a)
  | TmLam (Scope () Tm a)
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Tm
deriveShow1 ''Tm
makeBound ''Tm

lam :: Eq a => a -> Tm a -> Tm a
lam a = TmLam . abstract1 a

deriving instance Eq a => Eq (Tm a)
deriving instance Show a => Show (Tm a)