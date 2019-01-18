{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Scope (Scope, abstract1, fromScope, hoistScope, toScope)
import Bound.TH (makeBound)
import Data.Bifunctor (Bifunctor(..))
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Generics.Plated1 (Plated1(..))

import Label
import Ty

data Syn tyVar a
  -- | Type annotation
  --
  -- @x : T@
  = SynAnn (Syn tyVar a) (Ty tyVar)
  -- | Term variable
  -- @x@
  | SynVar a
  -- | Function elimination
  --
  -- @f x@
  | SynApp (Syn tyVar a) (Syn tyVar a)
  -- | Function introduction
  --
  -- @\x -> x@
  | SynLam (Scope () (Syn tyVar) a)

  -- | Empty record
  --
  -- @*{}@
  | SynEmpty

  -- | Record extension
  --
  -- @*{ l = _ | _ }@
  | SynExtend Label

  -- | Record selection
  --
  -- @_.l@
  | SynSelect Label

  -- | Record restriction
  --
  -- @_ - l@
  | SynRestrict Label

  -- | Variant matching
  --
  -- @+{ _ is l ? _ | _ }@
  | SynMatch Label

  -- | Variant injection
  --
  -- @+{ l = _ }@
  | SynInject Label

  -- | Variant embedding
  --
  -- @+{ l | _ }@
  | SynEmbed Label
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Syn
deriveShow1 ''Syn
makeBound ''Syn

instance Bifunctor Syn where
  bimap f g syn =
    case syn of
      SynAnn a b -> SynAnn (bimap f g a) (fmap f b)
      SynVar a -> SynVar $ g a
      SynApp a b -> SynApp (bimap f g a) (bimap f g b)
      SynLam s -> SynLam . hoistScope (first f) $ fmap g s
      SynEmpty -> SynEmpty
      SynExtend l -> SynExtend l
      SynSelect l -> SynSelect l
      SynRestrict l -> SynRestrict l
      SynMatch l -> SynMatch l
      SynInject l -> SynInject l
      SynEmbed l -> SynEmbed l

instance Plated1 (Syn tyVar) where
  plate1 f = go
    where
      go syn =
        case syn of
          SynAnn a b -> (\a' -> SynAnn a' b) <$> f a
          SynVar a -> pure $ SynVar a
          SynApp a b -> SynApp <$> f a <*> f b
          SynLam s -> SynLam . toScope <$> f (fromScope s)
          SynEmpty -> pure SynEmpty
          SynExtend l -> pure $ SynExtend l
          SynSelect l -> pure $ SynSelect l
          SynRestrict l -> pure $ SynRestrict l
          SynMatch l -> pure $ SynMatch l
          SynInject l -> pure $ SynInject l
          SynEmbed l -> pure $ SynEmbed l

lam :: Eq a => a -> Syn tyVar a -> Syn tyVar a
lam a = SynLam . abstract1 a

synExtend :: Label -> Syn tyVar a -> Syn tyVar a -> Syn tyVar a
synExtend l a = SynApp $ SynApp (SynExtend l) a

synMatch :: Syn tyVar a -> Label -> Syn tyVar a -> Syn tyVar a -> Syn tyVar a
synMatch a l b = SynApp $ SynApp (SynApp (SynMatch l) a) b

synRestrict :: Syn tyVar a -> Label -> Syn tyVar a
synRestrict syn l = SynApp (SynRestrict l) syn

synSelect :: Syn tyVar a -> Label -> Syn tyVar a
synSelect syn l = SynApp (SynSelect l) syn

synInject :: Label -> Syn tyVar a -> Syn tyVar a
synInject l = SynApp $ SynInject l

synEmbed :: Label -> Syn tyVar a -> Syn tyVar a
synEmbed l = SynApp $ SynEmbed l

selectFrom :: Label -> Syn tyVar a -> Maybe (Syn tyVar a)
selectFrom l = go
  where
    go (SynApp (SynApp (SynExtend l') val) rest) =
      if l == l'
      then Just val
      else go rest
    go _ = Nothing

deriving instance (Eq tyVar, Eq a) => Eq (Syn tyVar a)
deriving instance (Show tyVar, Show a) => Show (Syn tyVar a)