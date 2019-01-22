{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric #-}
{-# language TemplateHaskell #-}
module Kind where

import Bound.TH (makeBound)
import Control.Lens.Plated (Plated(..), gplate)
import GHC.Generics (Generic)

data Kind a
  = KindType
  | KindRow
  | KindConstraint
  | KindArr (Kind a) (Kind a)
  | KindVar a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)
makeBound ''Kind

instance Plated (Kind a) where; plate = gplate