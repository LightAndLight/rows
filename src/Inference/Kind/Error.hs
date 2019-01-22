{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, TemplateHaskell #-}
module Inference.Kind.Error where

import Control.Lens.TH (makeClassyPrisms)

import Kind

data KindError a
  = KindOccurs Int (Kind Int)
  | KindMismatch (Kind Int) (Kind Int)
  | KindVarNotFound a
  | KindCtorNotFound String
  deriving (Eq, Show)
makeClassyPrisms ''KindError

