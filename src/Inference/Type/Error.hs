{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, TemplateHaskell#-}
module Inference.Type.Error where

import Control.Lens.TH (makeClassyPrisms)
import Data.Void (Void)

import Inference.Kind.Error
import Kind
import Meta
import Ty

data TypeError a b c
  = TypeOccurs a (MetaT a Ty b)
  | TypeMismatch (MetaT a Ty b) (MetaT a Ty b)
  | TypeVarNotFound c
  | TypeKindMismatch (MetaT a Ty b) (Kind Void) (MetaT a Ty b) (Kind Void)
  | TypeCannotDeduce (MetaT a Ty b)
  | TypeKindError (KindError (Meta Int b))
  | TypeEscaped [Meta a b]
  deriving (Eq, Show)
makeClassyPrisms ''TypeError

instance AsKindError (TypeError a b c) (Meta Int b) where
  _KindError = _TypeKindError
