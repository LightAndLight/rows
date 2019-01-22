{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language RankNTypes #-}
module Inference.Type where

import Bound.Scope (instantiateVars, fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Concurrent.Supply (Supply)
import Control.Lens.Getter (use)
import Control.Monad (replicateM, unless)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Strict (runWriterT)
import Data.Bifunctor (first)
import Data.Coerce (coerce)
import Data.Foldable (toList)
import Data.Traversable (for)
import Data.Void (Void, absurd)

import qualified Data.Set as Set

import Evidence
import Inference.Evidence
import Inference.Kind
import Inference.State
import Inference.Type.Error
import Inference.Type.Monad
import Inference.Type.Row
import Kind
import Meta
import Tm
import Ty

occursType :: Eq meta => meta -> MetaT meta Ty a -> Bool
occursType v =
  foldr
    (\a b -> foldMeta (\_ -> (== v)) (\_ -> const False) (const False) a || b)
    False .
    unMetaT

-- | Find escaping skolems, if any
--
-- A skolem meta escapes if its depth is greater than the one provided
escapesType :: Int -> Ty (Meta meta a) -> [Meta meta a]
escapesType depth =
  filter
    (foldMeta (\_ -> const False) (\d -> const $ depth < d) (const False)) .
    toList

-- | Assumes that binders have been merged
--
-- i.e. there are no nested quantifiers like `forall a b c. forall d e f. g`,
-- and instead there are only flattened ones like `forall a b c d e f. g`
instanceOf
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Show tyVar, Ord tyVar
     )
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> Ty (Meta Int tyVar)
  -> Ty (Meta Int tyVar)
  -> TypeM s tyVar ev (KindM s' m) ()
instanceOf tyCtorCtx ty1 ty2 =
  deep $ do
    (skolems, s) <-
      case ty1 of
        TyForall n s ->
          (,) <$>
          replicateM n (newSkolem . KindVar =<< lift newKindMeta) <*>
          pure s
        _ -> pure ([], lift ty1)
    (metas, s') <-
      case ty2 of
        TyForall n s' ->
          (,) <$>
          replicateM n (newMeta . KindVar =<< lift newKindMeta) <*>
          pure s'
        _ -> pure ([], lift ty2)
    let
      ss = MetaT $ instantiateVars skolems s
      ss' = MetaT $ instantiateVars metas s'
    unifyType tyCtorCtx ss ss'

unifyType
  :: forall s s' tmVar tyVar ev m
   . ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar
     )
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> MetaT Int Ty tyVar
  -> MetaT Int Ty tyVar
  -> TypeM s tyVar ev (KindM s' m) ()
unifyType tyCtorCtx x y = do
  tyVarCtx <- use inferKinds
  x' <- unMetaT <$> findType x
  y' <- unMetaT <$> findType y
  xKind <-
    lift $
    inferKindM
      (fmap (fmap absurd) . tyCtorCtx)
      (\v -> maybe (Left v) Right $ tyVarCtx v)
      x'
  yKind <-
    lift $
    inferKindM
      (fmap (fmap absurd) . tyCtorCtx)
      (\v -> maybe (Left v) Right $ tyVarCtx v)
      y'
  lift $ unifyKind xKind yKind
  go x' y'
  where
    go ::
      Ty (Meta Int tyVar) ->
      Ty (Meta Int tyVar) ->
      TypeM s tyVar ev (KindM s' m) ()
    go TyArr TyArr = pure ()
    go TyRowEmpty TyRowEmpty = pure ()
    go TyRecord TyRecord = pure ()
    go TyVariant TyVariant = pure ()
    go TyInt TyInt = pure ()
    go (TyForall 0 s) ty =
      unifyType
        tyCtorCtx
        (MetaT $ instantiateVars [] s)
        (MetaT ty)
    go ty (TyForall 0 s) =
      unifyType
        tyCtorCtx
        (MetaT ty)
        (MetaT $ instantiateVars [] s)
    go (TyForall n s) (TyForall n' s') | n == n' =
      deep $ do
        skolems <- replicateM n $ newSkolem =<< KindVar <$> lift newKindMeta
        unifyType
          tyCtorCtx
          (MetaT $ instantiateVars skolems s)
          (MetaT $ instantiateVars skolems s')
    go (TyRowExtend l) (TyRowExtend l') | l == l' = pure ()
    go ty@(TyApp (TyApp (TyRowExtend l) t) r) s = do
      rewritten <- rewriteRow tyCtorCtx (rowTail r) l s
      case rewritten of
        Just (_, t', r') ->
          unifyType tyCtorCtx (MetaT t) (MetaT t') *>
          unifyType tyCtorCtx (MetaT r) (MetaT r')
        Nothing -> throwError $ TypeMismatch (MetaT ty) (MetaT s)
    go s t@(TyApp (TyApp TyRowExtend{} _) _) = go t s
    go (TyCtor s) (TyCtor s') | s == s' = pure ()
    go (TyVar (N a)) (TyVar (N b)) | a == b = pure ()
    go (TyVar (S _ a)) (TyVar (S _ b)) | a == b = pure ()
    go ty@(TyVar M{}) ty'@(TyVar M{}) = equateType (MetaT ty) (MetaT ty')
    go (TyApp a b) (TyApp a' b') =
      unifyType tyCtorCtx (MetaT a) (MetaT a') *>
      unifyType tyCtorCtx (MetaT b) (MetaT b')
    go ty'@(TyVar (M n a)) ty =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else
        case escapesType n ty of
          [] -> equateType (MetaT ty') (MetaT ty)
          metas -> throwError $ TypeEscaped metas
    go ty ty'@(TyVar (M n a)) =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else
        case escapesType n ty of
          [] -> equateType (MetaT ty) (MetaT ty')
          metas -> throwError $ TypeEscaped metas
    go l m = throwError $ TypeMismatch (MetaT l) (MetaT m)

contextFor
  :: (x -> Either tmVar (MetaT Int Ty tyVar))
  -> EvT ev (Tm (Meta Int tyVar)) x
  -> [MetaT Int Ty tyVar]
contextFor ctx = foldr (\a b -> either (const b) (: b) $ ctx a) []

generalize
  :: Ord tyVar
  => [MetaT Int Ty tyVar] -- ^ Variable context
  -> MetaT Int Ty tyVar -- ^ Term to generalize
  -> Ty (Meta Int tyVar)
generalize ctx (MetaT t) = forall_ minusContextMetas t
  where
    frees = toList t
    ctxMetas =
      foldr
        (\a b ->
           case unMetaT a of
             TyVar (M _ v) -> Set.insert v b
             _ -> b)
        Set.empty
        ctx
    minusContextMetas =
      filter (\case; M _ v -> Set.notMember v ctxMetas; _ -> True) frees

generalizeType
  :: forall s tyVar tmVar x m
   . ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar
     , Show tyVar, Show tmVar
     , Show x
     )
  => (x -> Either tmVar (MetaT Int Ty tyVar))
  -> (EvT Int (Tm (Meta Int tyVar)) x, MetaT Int Ty tyVar)
  -> TypeM s tyVar Int m (Tm Void x, Ty tyVar)
generalizeType varCtx (EvT tm, MetaT ty) = do
  (tm', constraints) <- finalizeEvidence tm
  ty' <-
    generalize (contextFor varCtx $ EvT tm) <$>
    findType (MetaT $ foldr (tyConstraint . unMetaT) ty constraints)
  case traverse (\case; N a -> Just a; _ -> Nothing) ty' of
    Nothing ->
      error $
      "generalizeType: unsolved metas:\n\n" <> show ty
    Just ty'' -> pure (stripAnnots tm', ty'')

applyEvidence
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar, Show x
     )
  => [MetaT Int Ty tyVar]
  -> EvT Int (Tm (Meta Int tyVar)) x
  -> TypeM s tyVar Int m (EvT Int (Tm (Meta Int tyVar)) x)
applyEvidence [] !a = pure a
applyEvidence (p:ps) (EvT !a) = do
  res <- fmap fst . runWriterT $ evidenceFor p
  EvT e <- maybe (EvT . TmVar <$> newEv p) pure res
  applyEvidence ps $ EvT (TmApp a e)

inferTypeM
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar, Show x
     )
  => (tmVar -> x)
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (x -> Either tmVar (MetaT Int Ty tyVar))
  -> EvT Int (Tm (Meta Int tyVar)) x
  -> TypeM s tyVar Int (KindM s' m) (EvT Int (Tm (Meta Int tyVar)) x, MetaT Int Ty tyVar)
inferTypeM ctx tyCtorCtx varCtx tm =
  case unEvT tm of
    TmAnn a ty -> do
      (EvT tm', aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      unifyType tyCtorCtx aTy (MetaT ty)
      pure (EvT $ TmAnn tm' ty, MetaT ty)
    TmVar E{} -> error "trying to infer type for evidence variable"
    TmVar (V a) -> do
      ty <- either (throwError . TypeVarNotFound) pure $ varCtx a
      let (ty', constraints) = coerce (stripConstraints $ unMetaT ty)
      tm' <- applyEvidence constraints tm
      pure (tm', ty')
    TmApp a b -> do
      (EvT a', aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      (EvT b', MetaT bTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT b
      retTy <- newMeta KindType
      unifyType
        tyCtorCtx
        aTy
        (MetaT $ TyApp (TyApp TyArr bTy) (TyVar retTy))
      pure (EvT $ TmApp a' b', MetaT $ TyVar retTy)
    TmAdd a b -> do
      (EvT a', aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      unifyType tyCtorCtx aTy (lift TyInt)
      (EvT b', bTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT b
      unifyType tyCtorCtx bTy (lift TyInt)
      pure (EvT $ TmAdd a' b', lift TyInt)
    TmRecord rs -> do
      res <- for rs $ \(l, v) -> do
        (v', vTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT v
        pure (l, v', vTy)
      pure
        ( EvT . TmRecord $ (\(l, EvT v, _) -> (l, v)) <$> res
        , MetaT . tyRecord $ foldr (\(l, _, MetaT vTy) -> tyRowExtend l vTy) TyRowEmpty res
        )
    TmLam s -> do
      argTy <- newMeta KindType
      (EvT body', MetaT bodyTy) <-
        inferTypeM
          (F . ctx)
          tyCtorCtx
          (unvar (const $ Right $ MetaT $ TyVar argTy) varCtx)
          (EvT $ sequence <$> fromScope s)
      bodyTy' <-
        case bodyTy of
          TyForall n sc -> do
            metas <- replicateM n $ newMeta =<< KindVar <$> lift newKindMeta
            pure $ instantiateVars metas sc
          _ -> pure bodyTy

      argTy' <- findType $ MetaT (TyVar argTy)
      unless (isMonotype $ unMetaT argTy') .
        throwError $ TypePolymorphicArg argTy'

      let tm' = EvT $ TmLam $ toScope $ sequence <$> body'
      pure
        ( tm'
        , MetaT $ generalize (contextFor varCtx tm') (MetaT $ tyArr (TyVar argTy) bodyTy')
        )
    TmSelect l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $ tyArr (tyRecord $ tyRowExtend l metaTy metaRow) metaTy
        )
    TmRestrict l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr (tyRecord $ tyRowExtend l metaTy metaRow) $
          tyRecord metaRow
        )
    TmExtend l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr metaTy $
          tyArr (tyRecord metaRow) $
          tyRecord (tyRowExtend l metaTy metaRow)
        )
    TmMatch l -> do
      metaA <- TyVar <$> newMeta KindType
      metaB <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr (tyVariant (tyRowExtend l metaA metaRow)) $
          tyArr (tyArr metaA metaB) $
          tyArr (tyArr (tyVariant metaRow) metaB) $
          metaB
        )
    TmInject l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr metaTy (tyVariant $ tyRowExtend l metaTy metaRow)
        )
    TmEmbed l -> do
      metaTy <- TyVar <$> newMeta KindType
      metaRow <- TyVar <$> newMeta KindRow
      tm' <- applyEvidence [MetaT $ tyOffset l metaRow] tm
      pure
        ( tm'
        , MetaT $
          tyArr metaRow (tyVariant $ tyRowExtend l metaTy metaRow)
        )
    TmInt n -> pure (EvT $ TmInt n, lift TyInt)

inferType
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar
     , Show tyVar
     , Show tmVar
     )
  => Supply -- ^ Name supply
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (tyVar -> Maybe (Kind Void)) -- ^ Type variables
  -> (tmVar -> Either tmVar (Ty tyVar)) -- ^ Term variables
  -> Tm tyVar tmVar
  -> m (Tm Void tmVar, Ty tyVar)
inferType supply tyCtorCtx tyVarCtx varCtx tm =
  runKindM supply
  (runTypeM
     (InferState
        { _inferSupply = supply
        , _inferEvidence = mempty
        , _inferKinds =
            foldMeta
              (\_ -> const Nothing)
              (\_ -> const Nothing)
              (fmap (fmap absurd) . tyVarCtx)
        , _inferDepth = 0
        })
     (generalizeType (fmap lift . varCtx) =<<
      inferTypeM
        id
        tyCtorCtx
        (fmap lift . varCtx)
        (lift $ first N tm)))
