{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Tm where

import Bound.Scope (Scope, abstract1, hoistScope)
import Bound.TH (makeBound)
import Data.Bifunctor (Bifunctor(..))
import Data.Deriving (deriveEq1, deriveShow1)

import Label
import Ty

data Tm tyVar a
  -- | Type annotation
  --
  -- @x : T@
  = TmAnn (Tm tyVar a) (Ty tyVar)
  -- | Term variable
  -- @x@
  | TmVar a
  -- | Function elimination
  --
  -- @f x@
  | TmApp (Tm tyVar a) (Tm tyVar a)
  -- | Function introduction
  --
  -- @\x -> x@
  | TmLam (Scope () (Tm tyVar) a)

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

instance Bifunctor Tm where
  bimap f g tm =
    case tm of
      TmAnn a b -> TmAnn (bimap f g a) (fmap f b)
      TmVar a -> TmVar $ g a
      TmApp a b -> TmApp (bimap f g a) (bimap f g b)
      TmLam s -> TmLam . hoistScope (first f) $ fmap g s
      TmEmpty -> TmEmpty
      TmExtend l -> TmExtend l
      TmSelect l -> TmSelect l
      TmRestrict l -> TmRestrict l
      TmMatch l -> TmMatch l
      TmInject l -> TmInject l
      TmEmbed l -> TmEmbed l

lam :: Eq a => a -> Tm tyVar a -> Tm tyVar a
lam a = TmLam . abstract1 a

tmExtend :: Label -> Tm tyVar a -> Tm tyVar a -> Tm tyVar a
tmExtend l a = TmApp $ TmApp (TmExtend l) a

tmMatch :: Tm tyVar a -> Label -> Tm tyVar a -> Tm tyVar a -> Tm tyVar a
tmMatch a l b = TmApp $ TmApp (TmApp (TmMatch l) a) b

tmRestrict :: Tm tyVar a -> Label -> Tm tyVar a
tmRestrict tm l = TmApp (TmRestrict l) tm

tmSelect :: Tm tyVar a -> Label -> Tm tyVar a
tmSelect tm l = TmApp (TmSelect l) tm

tmInject :: Label -> Tm tyVar a -> Tm tyVar a
tmInject l = TmApp $ TmInject l

tmEmbed :: Label -> Tm tyVar a -> Tm tyVar a
tmEmbed l = TmApp $ TmEmbed l

deriving instance (Eq tyVar, Eq a) => Eq (Tm tyVar a)
deriving instance (Show tyVar, Show a) => Show (Tm tyVar a)
