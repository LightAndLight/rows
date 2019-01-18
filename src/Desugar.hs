module Desugar where

import Bound.Scope (fromScope, toScope)

import Tm
import Syntax

desugar :: Syn tyVar a -> Tm tyVar a
desugar syn =
  case syn of
    SynAnn a b -> TmAnn (desugar a) b
    SynVar a -> TmVar a
    SynApp a b -> TmApp (desugar a) (desugar b)
    SynLam s -> TmLam $ toScope $ desugar $ fromScope s
    SynEmpty -> TmEmpty
    SynExtend l -> TmExtend l
    SynSelect l -> TmSelect l
    SynRestrict l -> TmRestrict l
    SynMatch l -> TmMatch l
    SynInject l -> TmInject l
    SynEmbed l -> TmEmbed l