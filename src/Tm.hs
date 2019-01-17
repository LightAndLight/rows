{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Tm where

import Bound.Scope (Scope, abstract1)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)

import Label

data Tm a
  -- | Term variable
  -- @x@
  = TmVar a
  -- | Function elimination
  --
  -- @f x@
  | TmApp (Tm a) (Tm a)
  -- | Function introduction
  --
  -- @\x -> x@
  | TmLam (Scope () Tm a)

  -- | Empty record
  --
  -- @*{}@
  | TmEmpty

  -- | Record extension
  --
  -- @*{ l = _ | _ }@
  | TmExtend Label

  -- | Record selection
  --
  -- @_.l@
  | TmSelect Label

  -- | Record restriction
  --
  -- @_ - l@
  | TmRestrict Label

  -- | Variant matching
  --
  -- @+{ _ is l ? _ | _ }@
  | TmMatch Label

  -- | Variant injection
  --
  -- @+{ l = _ }@
  | TmInject Label

  -- | Variant embedding
  --
  -- @+{ l | _ }@
  | TmEmbed Label
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Tm
deriveShow1 ''Tm
makeBound ''Tm

lam :: Eq a => a -> Tm a -> Tm a
lam a = TmLam . abstract1 a

deriving instance Eq a => Eq (Tm a)
deriving instance Show a => Show (Tm a)
