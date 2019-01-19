{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Tm where

import Bound.Scope (Scope, abstract1, hoistScope, toScope, fromScope)
import Bound.TH (makeBound)
import Data.Bifunctor (Bifunctor(..))
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Generics.Plated1 (Plated1(..))

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

  -- | Integer
  --
  -- @0@
  | TmInt !Int

  -- | Integer addition
  --
  -- @_ + _@
  | TmAdd (Tm tyVar a) (Tm tyVar a)
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Tm
deriveShow1 ''Tm
makeBound ''Tm

traverseTy
  :: forall m tyVar tyVar' tmVar
   . Applicative m
  => (Ty tyVar -> m (Ty tyVar'))
  -> Tm tyVar tmVar
  -> m (Tm tyVar' tmVar)
traverseTy f = go
  where
    go :: forall x. Tm tyVar x -> m (Tm tyVar' x)
    go tm =
      case tm of
        TmAnn a b -> TmAnn <$> go a <*> f b
        TmVar a -> pure $ TmVar a
        TmApp a b -> TmApp <$> go a <*> go b
        TmAdd a b -> TmAdd <$> go a <*> go b
        TmLam s -> TmLam . toScope <$> go (fromScope s)
        TmEmpty -> pure TmEmpty
        TmExtend l -> pure $ TmExtend l
        TmSelect l -> pure $ TmSelect l
        TmRestrict l -> pure $ TmRestrict l
        TmMatch l -> pure $ TmMatch l
        TmInject l -> pure $ TmInject l
        TmEmbed l -> pure $ TmEmbed l
        TmInt n -> pure $ TmInt n

instance Bifunctor Tm where
  bimap f g tm =
    case tm of
      TmAnn a b -> TmAnn (bimap f g a) (fmap f b)
      TmVar a -> TmVar $ g a
      TmApp a b -> TmApp (bimap f g a) (bimap f g b)
      TmAdd a b -> TmAdd (bimap f g a) (bimap f g b)
      TmLam s -> TmLam . hoistScope (first f) $ fmap g s
      TmEmpty -> TmEmpty
      TmExtend l -> TmExtend l
      TmSelect l -> TmSelect l
      TmRestrict l -> TmRestrict l
      TmMatch l -> TmMatch l
      TmInject l -> TmInject l
      TmEmbed l -> TmEmbed l
      TmInt n -> TmInt n

instance Plated1 (Tm tyVar) where
  plate1 f = go
    where
      go tm =
        case tm of
          TmAnn a b -> (\a' -> TmAnn a' b) <$> f a
          TmVar a -> pure $ TmVar a
          TmApp a b -> TmApp <$> f a <*> f b
          TmAdd a b -> TmAdd <$> f a <*> f b
          TmLam s -> TmLam . toScope <$> f (fromScope s)
          TmEmpty -> pure TmEmpty
          TmExtend l -> pure $ TmExtend l
          TmSelect l -> pure $ TmSelect l
          TmRestrict l -> pure $ TmRestrict l
          TmMatch l -> pure $ TmMatch l
          TmInject l -> pure $ TmInject l
          TmEmbed l -> pure $ TmEmbed l
          TmInt n -> pure $ TmInt n

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

selectFrom :: Label -> Tm tyVar a -> Maybe (Tm tyVar a)
selectFrom l = go
  where
    go (TmApp (TmApp (TmExtend l') val) rest) =
      if l == l'
      then Just val
      else go rest
    go _ = Nothing

deriving instance (Eq tyVar, Eq a) => Eq (Tm tyVar a)
deriving instance (Show tyVar, Show a) => Show (Tm tyVar a)
