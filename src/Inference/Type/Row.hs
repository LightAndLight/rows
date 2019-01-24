{-# language FlexibleContexts #-}
module Inference.Type.Row where

import Data.Void (Void)

import Inference.Type.Monad
import Kind
import Label
import Meta
import Ty

rowTail :: Show a => Ty (Meta Int a) -> Ty (Meta Int a)
rowTail (TyApp (TyApp TyRowExtend{} _) r) = r
rowTail (TyVar v) = TyVar v
rowTail TyRowEmpty = TyRowEmpty
rowTail _ = undefined

rewriteRow
  :: (Ord tyVar, Show tyVar)
  => (String -> Maybe (Kind Void))
  -> Ty (Meta Int tyVar) -- ^ row tail
  -> Label -- ^ desired label
  -> Ty (Meta Int tyVar) -- ^ term to rewrite
  -> TypeM s tyVar tmVar ev (Maybe (Label, Ty (Meta Int tyVar), Ty (Meta Int tyVar)))
rewriteRow tyCtorCtx rt ll ty =
  case ty of
    TyApp (TyApp (TyRowExtend l) t) r ->
      if ll == l
      then -- row-head
        pure $ Just (l, t, r)
      else do -- row-swap
        res <- rewriteRow tyCtorCtx rt ll r
        pure $ case res of
          Just (l', t', r') -> Just (l', t', tyRowExtend l t r')
          Nothing -> Nothing
    TyVar M{} -> -- row-var
      if ty == rt
      then error "infinite record"
      else do
        metaTy <- TyVar <$> newMetaInf KindType
        metaRow <- TyVar <$> newMetaInf KindRow
        equateType (MetaT ty) (MetaT $ tyRowExtend ll metaTy metaRow)
        pure $ Just (ll, metaTy, metaRow)
    _ -> pure Nothing
