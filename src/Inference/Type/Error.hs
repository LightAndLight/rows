{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, TemplateHaskell#-}
module Inference.Type.Error where

import Control.Lens.TH (makeClassyPrisms)
import Data.Void (Void)

import Inference.Kind.Error
import Kind
import Meta
import Ty

data TypeError a b c
  = TypeOccurs a (DisplayMetaT a Ty b)
  | TypeMismatch (DisplayMetaT a Ty b) (DisplayMetaT a Ty b)
  | TypeVarNotFound c
  | TypeKindMismatch (DisplayMetaT a Ty b) (Kind Void) (DisplayMetaT a Ty b) (Kind Void)
  | TypeCannotDeduce (DisplayMetaT a Ty b) [DisplayMetaT a Ty b]
  | TypeKindError (KindError (DisplayMeta Int b))
  | TypeEscaped [DisplayMetaT a Ty b]
  | TypePolymorphicArg (DisplayMetaT a Ty b)
  deriving (Eq, Show)
makeClassyPrisms ''TypeError

instance AsKindError (TypeError a b c) (DisplayMeta Int b) where
  _KindError = _TypeKindError
