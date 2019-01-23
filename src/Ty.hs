{-# language BangPatterns #-}
{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric #-}
{-# language FlexibleContexts #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Ty where

import Bound.Scope (Scope, abstract)
import Bound.TH (makeBound)
import Control.Lens.Fold (allOf)
import Control.Lens.Plated (Plated(..), gplate)
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)
import Data.List (elemIndex)
import Data.Set (Set)
import GHC.Generics (Generic)

import qualified Data.Set as Set

import Label

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

  -- | Universal quantification
  --
  -- @forall x_1 x_2 ... x_n. _@
  | TyForall !Int (Scope Int Ty a)

  -- | Existential quantification
  --
  -- @exists x_1 x_2 ... x_n. _@
  | TyExists !Int (Scope Int Ty a)
  deriving (Functor, Foldable, Traversable, Generic)
deriveEq1 ''Ty
deriveOrd1 ''Ty
deriveShow1 ''Ty
makeBound ''Ty
deriving instance Eq a => Eq (Ty a)
deriving instance Show a => Show (Ty a)

instance Plated (Ty a) where; plate = gplate

isMonotype :: Ty a -> Bool
isMonotype ty =
  (case ty of; TyForall{} -> False; _ -> True) &&
  allOf plate isMonotype ty

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

unfoldApps :: Ty a -> (Int, Ty a, [Ty a])
unfoldApps = go 0 []
  where
    go !n xs (TyApp a b) = go (n+1) (b:xs) a
    go !n xs a = (n, a, xs)

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
      TyExists{} -> (ty, [])
      TyForall{} -> (ty, [])

ordNub
  :: Ord a
  => Set a -- ^ Set of all the elements in the list
  -> [a] -- ^ The list to nub
  -> [a]
ordNub _ [] = []
ordNub set (x:xs) =
  if x `Set.member` set
  then x : ordNub (Set.delete x set) xs
  else ordNub set xs

forall_ :: Ord a => [a] -> Ty a -> Ty a
forall_ as ty =
  TyForall (Set.size asSet) $
  abstract (`elemIndex` ordNub asSet as) ty
  where
    asSet = Set.fromList as

exists_ :: Ord a => [a] -> Ty a -> Ty a
exists_ as ty =
  TyExists (Set.size asSet) $
  abstract (`elemIndex` ordNub asSet as) ty
  where
    asSet = Set.fromList as
