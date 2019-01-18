{-# language BangPatterns #-}
{-# language RankNTypes #-}
{-# language ViewPatterns #-}
module Desugar.Sections where

import Bound.Scope (fromScope, toScope)
import Bound.Var (Var(..), unvar)

import Syntax

merge :: (Int, Syn tyVar a) -> (Int, Syn tyVar a) -> (Int, Syn tyVar a)
merge (0, x) (0, y) = (0, SynApp x y)
merge (0, x) (!n, SynLam (fromScope -> s)) =
  let
    (n', tm) = merge (0, F <$> x) (n-1, s)
  in
    (n'+1, SynLam $ toScope tm)
merge (!m, SynLam (fromScope -> s)) (!n, y) =
  let
    (m', tm) = merge (m-1, s) (n, F <$> y)
  in
    (m'+1, SynLam $ toScope tm)
merge _ _ = error "merge: invalid arguments"

shunt
  :: (forall x. Syn tyVar x -> Syn tyVar x)
  -> (Int, Syn tyVar a)
  -> (Int, Syn tyVar a)
shunt f (0, tm) = (0, f tm)
shunt f (!n, SynLam (fromScope -> s)) =
  let
    (n', tm) = shunt f (n-1, s)
  in
    (n'+1, SynLam $ toScope tm)
shunt _ _ = error "shunt: invalid arguments"

wedge
  :: (Var () a -> Var () a)
  -> (Int, Syn tyVar (Var () a))
  -> (Int, Syn tyVar a)
wedge f (0, s) = (0, SynLam $ toScope $ f <$> s)
wedge f (!n, SynLam (fromScope -> s)) =
  let
    (n', tm) = wedge (unvar (F . B) (fmap F . f)) (n-1, s)
  in
    (n'+1, SynLam $ toScope tm)
wedge _ _ = error "wedge: invalid arguments"

makeSections :: Syn tyVar a -> Syn tyVar a
makeSections = snd . go
  where
    go :: Syn tyVar a -> (Int, Syn tyVar a)
    go syn =
      case syn of
        SynUnknown -> (1, SynLam $ toScope $ pure (B ()))
        SynApp a b -> merge (go a) (go b)
        SynAnn a b -> shunt (\x -> SynAnn x b) (go a)
        SynVar{} -> (0, syn)
        SynEmpty -> (0, syn)
        SynExtend{} -> (0, syn)
        SynSelect{} -> (0, syn)
        SynRestrict{} -> (0, syn)
        SynMatch{} -> (0, syn)
        SynInject{} -> (0, syn)
        SynEmbed{} -> (0, syn)
        SynLam (fromScope -> s) -> wedge id (go s)
        SynParens a -> (0, SynParens . snd $ go a)