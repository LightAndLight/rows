{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric #-}
{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module Ty where

import Bound.Scope (Scope, abstract)
import Bound.TH (makeBound)
import Control.Lens.Plated (Plated(..), gplate)
import Control.Lens.Wrapped (_Wrapped, _Unwrapped)
import Control.Monad ((<=<))
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)
import Data.Equivalence.Monad (MonadEquiv, classDesc)
import Data.List (elemIndex)
import GHC.Generics (Generic)

import qualified Data.Set as Set

import Label
import Meta

data Ty a
  -- | Arrow type
  --
  -- @(->)@
  = TyArr

  -- | Type constructor
  --
  -- @X@
  | TyCtor String

  -- | Type variable
  --
  -- @x@
  | TyVar a

  -- | Type application
  --
  -- @X Y@
  | TyApp (Ty a) (Ty a)

  -- | Empty row
  --
  -- @()@
  | TyRowEmpty

  -- | Row extension
  --
  -- @(l : _ | _)@
  | TyRowExtend Label

  -- | Record
  --
  -- @Record@
  | TyRecord

  -- | Variant
  --
  -- @Variant@
  | TyVariant

  -- | Row offset
  --
  -- @(l | _)@
  | TyOffset Label

  -- | Constraint arrow
  --
  -- @_ => _@
  | TyConstraint

  -- | Integer
  --
  -- @Int@
  | TyInt
  deriving (Eq, Show, Functor, Foldable, Traversable, Generic)
deriveEq1 ''Ty
deriveOrd1 ''Ty
deriveShow1 ''Ty
makeBound ''Ty

instance Plated (Ty a) where; plate = gplate

tyArr :: Ty a -> Ty a -> Ty a
tyArr a = TyApp $ TyApp TyArr a

tyConstraint :: Ty a -> Ty a -> Ty a
tyConstraint a = TyApp $ TyApp TyConstraint a

tyRowExtend :: Label -> Ty a -> Ty a -> Ty a
tyRowExtend l a = TyApp $ TyApp (TyRowExtend l) a

tyRecord :: Ty a -> Ty a
tyRecord = TyApp TyRecord

tyVariant :: Ty a -> Ty a
tyVariant = TyApp TyVariant

tyOffset :: Label -> Ty a -> Ty a
tyOffset l = TyApp $ TyOffset l

stripConstraints :: Ty a -> (Ty a, [Ty a])
stripConstraints ty =
  -- if we introduce first-class polymorphism, then we can't float
  -- constraints from under a forall
    case ty of
      TyApp (TyApp TyConstraint c) rest -> (c :) <$> stripConstraints rest
      TyApp{} -> (ty, [])
      TyArr -> (ty, [])
      TyCtor{} -> (ty, [])
      TyVar{} -> (ty, [])
      TyRowEmpty -> (ty, [])
      TyRowExtend{} -> (ty, [])
      TyRecord -> (ty, [])
      TyVariant -> (ty, [])
      TyOffset{} -> (ty, [])
      TyConstraint -> (ty, [])
      TyInt -> (ty, [])

findType
  :: MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
  => MetaT Int Ty tyVar -> m (MetaT Int Ty tyVar)
findType = _Wrapped go
  where
    go = plate go <=< _Unwrapped classDesc

data Forall a
  = Forall
  { _forallSize :: !Int
  , _forallType :: Scope Int Ty a
  } deriving (Eq, Show)

forAll
  :: Ord a
  => [a]
  -> Ty a
  -> Forall a
forAll as ty =
  Forall
    (Set.size $ Set.fromList as)
    (abstract (`elemIndex` as) ty)
