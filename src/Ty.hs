{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language TemplateHaskell #-}
module Ty where

import Bound.Scope (Scope)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)

data Ty a
  = TyArr
  | TyCtor String
  | TyVar a
  | TyApp (Ty a) (Ty a)
  deriving (Eq, Show, Functor, Foldable, Traversable)
deriveEq1 ''Ty
deriveOrd1 ''Ty
deriveShow1 ''Ty
makeBound ''Ty

data Forall a
  = Forall !Int (Scope Int Ty a)
  deriving (Eq, Ord, Show)
