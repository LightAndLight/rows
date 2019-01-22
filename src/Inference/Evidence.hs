{-# language FlexibleContexts #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
module Inference.Evidence where

import Bound.Scope (abstract)
import Control.Lens.Getter (use)
import Control.Monad.Except (MonadError)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Strict (WriterT, runWriterT, tell)
import Data.Either (partitionEithers)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Traversable (for)

import qualified Data.Sequence as Seq

import Evidence
import Inference.State
import Inference.Type.Error
import Inference.Type.Monad
import Meta
import Tm
import Ty

evidenceFor
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar
     )
  => MetaT Int Ty tyVar
  -> WriterT
       (Seq (EvEntry Int tyVar Int))
       (TypeM s tyVar Int m)
       (Maybe (EvT Int (Tm (Meta Int tyVar)) x))
evidenceFor ty = do
  ty' <- lift $ findType ty
  case unMetaT ty' of
    TyApp TyOffset{} TyRowEmpty -> pure . Just . EvT $ TmInt 0
    TyApp (TyOffset l) (TyApp (TyApp (TyRowExtend l') _) rest) -> do
      let super = MetaT $ TyApp (TyOffset l) rest
      res <- evidenceFor super
      e <-
        maybe
          (do
              e' <- newEv super
              tell [EvEntry (foldEv id undefined e') super]
              pure $ TmVar e')
          (pure . unEvT)
          res
      pure . Just . EvT $
        if l < l'
        then e
        else TmAdd (TmInt 1) e
    _ -> pure Nothing

getEvidence
  :: forall s tyVar tmVar m x
   . ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar
     )
  => TypeM s tyVar Int m
       ( [(Int, EvT Int (Tm (Meta Int tyVar)) x)]
       , [(Int, MetaT Int Ty tyVar)]
       )
getEvidence = use inferEvidence >>= go
  where
    go
      :: Seq (EvEntry Int tyVar Int)
      -> TypeM s tyVar Int m
           ( [(Int, EvT Int (Tm (Meta Int tyVar)) x)]
           , [(Int, MetaT Int Ty tyVar)]
           )
    go evs | Seq.null evs = pure mempty
    go evs = do
      (evs', more) <-
        runWriterT $
        for evs $ \(EvEntry e ty) ->
          maybe (Right (e, ty)) (Left . (,) e) <$> evidenceFor ty
      (partitionEithers (toList evs') <>) <$> go more

finalizeEvidence
  :: forall s tyVar tmVar x m
   . ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar
     , Show tyVar, Show tmVar
     , Show x
     )
  => Tm (Meta Int tyVar) (Ev Int x)
  -> TypeM s tyVar Int m (Tm (Meta Int tyVar) x, [MetaT Int Ty tyVar])
finalizeEvidence tm = do
  (sat, unsat) <- getEvidence
  let
    (unsatVals, unsatTypes) = unzip unsat
    tm' = tm >>= foldEv (\x -> maybe (pure $ E x) unEvT $ lookup x sat) (pure . V)
    tm'' =
      foldr
        (\a ->
           TmLam .
           abstract
             (foldEv
                (\x -> if x == a then Just () else Nothing)
                (const Nothing)))
        tm'
        unsatVals
  either
    (\x -> error $ "un-abstracted evidence: " <> show x <> "\n\n" <> show unsatVals)
    (\x -> pure (x, unsatTypes))
    (traverse (foldEv Left Right) tm'')
