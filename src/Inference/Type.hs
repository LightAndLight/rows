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
import Data.Foldable (toList, traverse_)
import Data.Traversable (for)
import Data.Void (Void, absurd)

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
    (\a b -> foldMeta (== v) (const False) (const False) a || b)
    False .
    unMetaT

-- | Find escaping skolems, if any
--
-- A skolem meta escapes if its depth is greater than the one provided
escapesType :: Int -> Ty (Meta meta a) -> [Meta meta a]
escapesType depth =
  filter
    (\case; S d _ -> depth < d; _ -> False) .
    toList

instantiateTyWith
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar
     )
  => (Kind Int -> TypeM s tyVar ev (KindM s' m) (Meta Int tyVar))
  -> MetaT Int Ty tyVar
  -> TypeM s tyVar ev (KindM s' m)
       ( [Meta Int tyVar]
       , [MetaT Int Ty tyVar]
       , MetaT Int Ty tyVar
       )
instantiateTyWith f ty = do
  (metas, ty') <-
    case unMetaT ty of
      TyForall n s -> do
        metas <- replicateM n $ f =<< KindVar <$> lift newKindMeta
        pure (metas, instantiateVars metas s)
      x -> pure ([], x)
  let (ty'', constraints) = coerce (stripConstraints ty')
  pure (metas, constraints, ty'')

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
    (_, constraints1, s) <- instantiateTyWith newSkolem $ MetaT ty1
    (_, constraints2, s') <- instantiateTyWith newMetaInf $ MetaT ty2
    unifyType tyCtorCtx s s'
    constraints1' <- traverse findType constraints1
    constraints2' <- traverse findType constraints2
    traverse_ (constraints1' `entails`) constraints2'

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
    go ty'@(TyVar (M n _ a)) ty =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else
        case escapesType n ty of
          [] -> equateType (MetaT ty') (MetaT ty)
          metas -> throwError $ TypeEscaped metas
    go ty ty'@(TyVar (M n _ a)) =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else
        case escapesType n ty of
          [] -> equateType (MetaT ty) (MetaT ty')
          metas -> throwError $ TypeEscaped metas
    go l m = throwError $ TypeMismatch (MetaT l) (MetaT m)

generalize
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar, Show tmVar, Show x
     )
  => Tm (Meta Int tyVar) (Ev Int x) -- ^ Term to generalize
  -> MetaT Int Ty tyVar -- ^ Type to generalize
  -> TypeM s tyVar Int m (Tm (Meta Int tyVar) x, Ty (Meta Int tyVar))
generalize tm (MetaT t) = do
  rank <- Rank <$> use inferRank
  (tm', constraints) <- finalizeEvidence tm
  let ty' = foldr (tyConstraint . unMetaT) t constraints
  pure (tm', forall_ (vars rank ty') ty')
  where
    vars rank ty =
      foldr
        (\a b ->
           case a of
             M _ r _ | r > rank -> a : b
             _ -> b)
        []
        ty

instantiateWith
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar, Show x
     )
  => (Kind Int -> TypeM s tyVar Int (KindM s' m) (Meta Int tyVar))
  -> EvT Int (Tm (Meta Int tyVar)) x
  -> MetaT Int Ty tyVar
  -> TypeM s tyVar Int (KindM s' m)
       ( [Meta Int tyVar]
       , EvT Int (Tm (Meta Int tyVar)) x
       , MetaT Int Ty tyVar
       )
instantiateWith f tm ty = do
  (metas, constraints, ty') <- instantiateTyWith f ty
  tm' <- applyEvidence constraints tm
  pure (metas, tm', ty')

instantiate
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar, Show x
     )
  => EvT Int (Tm (Meta Int tyVar)) x
  -> MetaT Int Ty tyVar
  -> TypeM s tyVar Int (KindM s' m)
       ( [Meta Int tyVar]
       , EvT Int (Tm (Meta Int tyVar)) x
       , MetaT Int Ty tyVar
       )
instantiate = instantiateWith newMetaInf

closeType ::
  (Show tyVar, Show x) =>
  EvT Int (Tm (Meta Int tyVar)) x ->
  MetaT Int Ty tyVar ->
  (Tm Void x, Ty tyVar)
closeType (EvT tm) (MetaT ty) = do
  case traverse (\case; N a -> Just a; _ -> Nothing) ty of
    Nothing ->
      error $
      "closeType: unsolved metas:\n\n" <> show ty
    Just ty' ->
      case traverse (\case; V a -> Just a; _ -> Nothing) tm of
        Nothing ->
          error $
          "closeType: unsolved evidence:\n\n" <> show tm
        Just tm' -> (stripAnnots tm', ty')

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

funmatch ::
  ( MonadError (TypeError Int tyVar ev) m
  , Show tyVar, Ord tyVar
  ) =>
  (String -> Maybe (Kind Void)) -> -- ^ Type constructors
  MetaT Int Ty tyVar ->
  TypeM s tyVar Int (KindM s' m) (MetaT Int Ty tyVar, MetaT Int Ty tyVar)
funmatch tyCtorCtx (MetaT ty) =
  case ty of
    TyApp (TyApp TyArr i) o -> pure (MetaT i, MetaT o)
    _ -> do
      inTy <- TyVar <$> newMetaInf KindType
      outTy <- TyVar <$> newMetaInf KindType
      unifyType tyCtorCtx (MetaT ty) (MetaT $ tyArr inTy outTy)
      pure (MetaT inTy, MetaT outTy)

inferTypeM
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , Ord tyVar, Show tyVar, Show tmVar, Show x
     )
  => (tmVar -> x)
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (x -> Either tmVar (MetaT Int Ty tyVar))
  -> EvT Int (Tm (Meta Int tyVar)) x
  -> TypeM s tyVar Int (KindM s' m) (EvT Int (Tm (Meta Int tyVar)) x, MetaT Int Ty tyVar)
inferTypeM ctx tyCtorCtx varCtx tm =
  case unEvT tm of
    TmAnn a ty -> do
      (EvT tm', MetaT aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      instanceOf tyCtorCtx ty aTy
      pure (EvT $ TmAnn tm' ty, MetaT ty)
    TmVar E{} -> error "trying to infer type for evidence variable"
    TmVar (V a) -> do
      (_, tm', ty') <-
        instantiate tm =<<
        either (throwError . TypeVarNotFound) pure (varCtx a)
      pure (tm', ty')
    TmApp a b -> do
      (aTm, aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a

      (_, EvT aTm', aTy') <- instantiate aTm aTy
      (MetaT inTy, outTy) <- funmatch tyCtorCtx aTy'

      (EvT bTm, MetaT bTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT b

      instanceOf tyCtorCtx bTy inTy

      let tm' = TmApp aTm' bTm
      ty' <- findType outTy
      (tm'', ty'') <- generalize tm' ty'

      pure (lift tm'', MetaT ty'')
    TmAdd a b -> do
      (EvT a', aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      unifyType tyCtorCtx aTy (lift TyInt)
      (EvT b', bTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT b
      unifyType tyCtorCtx bTy (lift TyInt)
      pure (EvT $ TmAdd a' b', lift TyInt)
    TmRecord rs -> do
      res <-
        for rs $ \(l, v) -> do
          (v', vTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT v
          pure (l, v', vTy)

      ty' <-
        findType . MetaT $
        tyRecord $
        foldr (\(l, _, MetaT vTy) -> tyRowExtend l vTy) TyRowEmpty res

      let tm' = TmRecord $ (\(l, EvT v, _) -> (l, v)) <$> res
      (tm'', ty'') <- generalize tm' ty'

      pure
        ( lift tm''
        , MetaT ty''
        )
    TmLam s -> do
      (argTy, bodyTm, bodyTy) <-
        ranked $ do
          argTy <- newMetaRank KindType
          (body, bodyTy) <-
            inferTypeM
              (F . ctx)
              tyCtorCtx
              (unvar (const $ Right $ MetaT $ TyVar argTy) varCtx)
              (EvT $ sequence <$> fromScope s)
          pure (argTy, body, bodyTy)

      (_, EvT bodyTm', MetaT bodyTy') <- instantiate bodyTm bodyTy

      MetaT argTy' <- findType $ MetaT (TyVar argTy)
      unless (isMonotype argTy') .
        throwError $ TypePolymorphicArg (MetaT argTy')

      p <- findType $ MetaT $ tyArr argTy' bodyTy'

      let tm' = TmLam $ toScope $ sequence <$> bodyTm'
      (tm'', ty') <- generalize tm' p
      pure
        ( lift tm''
        , MetaT ty'
        )
    TmSelect l -> do
      metaTy <- newMetaInf KindType
      pure
        ( tm
        , MetaT $
          -- TyForall 2 . toScope $
          TyForall 1 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          -- tyArr (tyRecord $ tyRowExtend l (pure $ B 1) (pure $ B 0)) $
          tyArr (tyRecord $ tyRowExtend l (pure $ F metaTy) (pure $ B 0)) $
          -- pure (B 1)
          pure (F metaTy)
        )
    TmRestrict l -> do
      pure
        ( tm
        , MetaT $
          TyForall 2 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (tyRecord $ tyRowExtend l (pure $ B 1) (pure $ B 0)) $
          tyRecord (pure $ B 0)
        )
    TmExtend l -> do
      pure
        ( tm
        , MetaT $
          TyForall 2 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (pure $ B 1) $
          tyArr (tyRecord (pure $ B 0)) $
          tyRecord (tyRowExtend l (pure $ B 1) (pure $ B 0))
        )
    TmMatch l -> do
      pure
        ( tm
        , MetaT $
          TyForall 3 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (tyVariant (tyRowExtend l (pure $ B 1) (pure $ B 0))) $
          tyArr (tyArr (pure $ B 1) (pure $ B 2)) $
          tyArr (tyArr (tyVariant (pure $ B 0)) (pure $ B 2)) $
          pure (B 2)
        )
    TmInject l -> do
      pure
        ( tm
        , MetaT $
          TyForall 2 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (pure $ B 1) $
          tyVariant (tyRowExtend l (pure $ B 1) (pure $ B 0))
        )
    TmEmbed l -> do
      pure
        ( tm
        , MetaT $
          TyForall 2 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (pure $ B 0) $
          tyVariant (tyRowExtend l (pure $ B 1) (pure $ B 0))
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
              (const Nothing)
              (const Nothing)
              (fmap (fmap absurd) . tyVarCtx)
        , _inferDepth = 0
        , _inferRank = 1
        })
     (uncurry closeType <$>
      inferTypeM
        id
        tyCtorCtx
        (fmap lift . varCtx)
        (lift $ first N tm)))
