{-# language BangPatterns #-}
{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
module Inference.Type where

import Bound.Scope (instantiateVars, fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Concurrent.Supply (Supply)
import Control.Lens.Getter (use)
import Control.Monad (replicateM, unless)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (first)
import Data.Bitraversable (bitraverse)
import Data.Coerce (coerce)
import Data.Foldable (traverse_)
import Data.Maybe (fromJust)
import Data.Traversable (for)
import Data.Void (Void, absurd)

import Data.List.Utils
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

occursType :: Eq meta => meta -> MetaT 'Check meta Ty a -> Bool
occursType v =
  foldr
    (\a b -> foldMeta (== v) (const False) (const False) a || b)
    False .
    unMetaT

-- | Find escaping skolems, if any
--
-- A skolem meta escapes if its depth is greater than the one provided
escapesType ::
  Int ->
  Ty (Meta 'Check meta tyVar) ->
  TypeM s tyVar tmVar [Meta 'Check meta tyVar]
escapesType depth = filterM (fmap (maybe False (depth <)) . skolemDepth)

instantiateTyWith
  :: (Ord tyVar, Show tyVar)
  => (Kind Int -> KindM s' (TypeM s tyVar tmVar) (Meta 'Check Int tyVar))
  -> MetaT 'Check Int Ty tyVar
  -> KindM s'
       (TypeM s tyVar tmVar)
       ( [Meta 'Check Int tyVar]
       , [MetaT 'Check Int Ty tyVar]
       , MetaT 'Check Int Ty tyVar
       )
instantiateTyWith f ty = do
  (metas, ty') <-
    case unMetaT ty of
      TyForall n s -> do
        metas <- replicateM n $ f =<< KindVar <$> newKindMeta
        pure (metas, instantiateVars metas s)
      x -> pure ([], x)
  let (ty'', constraints) = coerce (stripConstraints ty')
  pure (metas, constraints, ty'')

-- | Assumes that binders have been merged
--
-- i.e. there are no nested quantifiers like `forall a b c. forall d e f. g`,
-- and instead there are only flattened ones like `forall a b c d e f. g`
instanceOf
  :: (Show tyVar, Ord tyVar)
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> Ty (Meta 'Check Int tyVar)
  -> Ty (Meta 'Check Int tyVar)
  -> KindM s' (TypeM s tyVar tmVar) ()
instanceOf tyCtorCtx ty1 ty2 =
  deep $ do
    (_, constraints1, s) <- instantiateTyWith (lift . newSkolem) $ MetaT ty1
    (_, constraints2, s') <- instantiateTyWith (lift . newMetaInf) $ MetaT ty2
    unifyType tyCtorCtx s s'
    constraints1' <- lift $ traverse findType constraints1
    constraints2' <- lift $ traverse findType constraints2
    lift $ traverse_ (constraints1' `entails`) constraints2'

unifyType
  :: forall s s' tmVar tyVar
    . (Ord tyVar, Show tyVar)
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> MetaT 'Check Int Ty tyVar
  -> MetaT 'Check Int Ty tyVar
  -> KindM s' (TypeM s tyVar tmVar) ()
unifyType tyCtorCtx x y = do
  tyVarCtx <- use inferKinds
  x' <- lift $ unMetaT <$> findType x
  y' <- lift $ unMetaT <$> findType y
  xKind <-
    inferKindM
      (fmap (fmap absurd) . tyCtorCtx)
      (\v -> maybe (Left <$> displayTypeM v) (pure . Right) $ tyVarCtx v)
      x'
  yKind <-
    inferKindM
      (fmap (fmap absurd) . tyCtorCtx)
      (\v -> maybe (Left <$> displayTypeM v) (pure . Right) $ tyVarCtx v)
      y'
  unifyKind xKind yKind
  go x' y'
  where
    go ::
      Ty (Meta 'Check Int tyVar) ->
      Ty (Meta 'Check Int tyVar) ->
      KindM s' (TypeM s tyVar tmVara) ()
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
        skolems <- replicateM n $ lift . newSkolem =<< KindVar <$> newKindMeta
        unifyType
          tyCtorCtx
          (MetaT $ instantiateVars skolems s)
          (MetaT $ instantiateVars skolems s')
    go (TyRowExtend l) (TyRowExtend l') | l == l' = pure ()
    go ty@(TyApp (TyApp (TyRowExtend l) t) r) s = do
      rewritten <- lift $ rewriteRow tyCtorCtx (rowTail r) l s
      case rewritten of
        Just (_, t', r') ->
          unifyType tyCtorCtx (MetaT t) (MetaT t') *>
          unifyType tyCtorCtx (MetaT r) (MetaT r')
        Nothing -> do
          dTy <- lift . displayType $ MetaT ty
          dS <- lift . displayType $ MetaT s
          throwError $ TypeMismatch dTy dS
    go s t@(TyApp (TyApp TyRowExtend{} _) _) = go t s
    go (TyCtor s) (TyCtor s') | s == s' = pure ()
    go (TyVar (N a)) (TyVar (N b)) | a == b = pure ()
    go (TyVar (S _ a)) (TyVar (S _ b)) | a == b = pure ()
    go ty@(TyVar M{}) ty'@(TyVar M{}) = lift $ equateType (MetaT ty) (MetaT ty')
    go (TyApp a b) (TyApp a' b') =
      unifyType tyCtorCtx (MetaT a) (MetaT a') *>
      unifyType tyCtorCtx (MetaT b) (MetaT b')
    go ty'@(TyVar v@(M _ _ a)) ty = do
      d <- lift $ fromJust <$> metaDepth v
      if occursType a $ MetaT ty
      then do
        dTy <- lift . displayType $ MetaT ty
        throwError $ TypeOccurs a dTy
      else do
        escs <- lift $ escapesType d ty
        case escs of
          [] -> lift $ equateType (MetaT ty') (MetaT ty)
          metas -> do
            dMetas <- lift $ traverse (displayType . MetaT . TyVar) metas
            throwError $ TypeEscaped dMetas
    go ty ty'@(TyVar M{}) = go ty' ty
    go l m = do
      dL <- lift . displayType $ MetaT l
      dM <- lift . displayType $ MetaT m
      throwError $ TypeMismatch dL dM

generalize ::
  (Ord tyVar, Show tyVar, Show tmVar) =>
  (tmVar -> x) ->
  EvT (Tm (Meta 'Check Int tyVar)) x -> -- ^ Term to generalize
  MetaT 'Check Int Ty tyVar -> -- ^ Type to generalize
  TypeM s tyVar tmVar
    ( EvT (Tm (Meta 'Check Int tyVar)) x
    , MetaT 'Check Int Ty tyVar
    )
generalize ctx tm ty = do
  tm' <- solvePlaceholders ctx tm
  (tm'', constraints) <- abstractEvidence tm'
  let ty' = foldr (tyConstraint . unMetaT) (unMetaT ty) constraints
  rank <- Rank <$> use inferRank
  vars <- filterM (fmap (maybe False (>= rank)) . metaRank) ty'
  let ty'' = forall_ vars ty'
  pure (tm'', MetaT ty'')

instantiateWith
  :: (Ord tyVar, Show tyVar, Show x)
  => (tmVar -> x)
  -> (Kind Int -> KindM s' (TypeM s tyVar tmVar) (Meta 'Check Int tyVar))
  -> EvT (Tm (Meta 'Check Int tyVar)) x
  -> MetaT 'Check Int Ty tyVar
  -> KindM s' (TypeM s tyVar tmVar)
       ( [Meta 'Check Int tyVar]
       , EvT (Tm (Meta 'Check Int tyVar)) x
       , MetaT 'Check Int Ty tyVar
       )
instantiateWith ctx f tm ty = do
  (metas, constraints, ty') <- instantiateTyWith f ty
  tm' <- applyEvidence ctx constraints tm
  pure (metas, tm', ty')

instantiate ::
  (Ord tyVar, Show tyVar, Show x) =>
  (tmVar -> x) ->
  EvT (Tm (Meta 'Check Int tyVar)) x ->
  MetaT 'Check Int Ty tyVar ->
  KindM s' (TypeM s tyVar tmVar)
    ( [Meta 'Check Int tyVar]
    , EvT (Tm (Meta 'Check Int tyVar)) x
    , MetaT 'Check Int Ty tyVar
    )
instantiate ctx = instantiateWith ctx (lift . newMetaInf)

closeType ::
  (Ord tyVar, Show tyVar, Show tmVar, Show x) =>
  (tmVar -> x) ->
  EvT (Tm (Meta 'Check Int tyVar)) x ->
  MetaT 'Check Int Ty tyVar ->
  TypeM s tyVar tmVar (Tm Void x, Ty tyVar)
closeType ctx tm ty = do
  (EvT tm', MetaT ty') <- generalize ctx tm ty
  case traverse (\case; N a -> Just a; _ -> Nothing) ty' of
    Nothing -> do
      dTy <- showMetaT $ MetaT ty'
      error $ "closeType: unsolved metas:\n\n" <> dTy
    Just ty'' ->
      case traverse (\case; V a -> Just a; _ -> Nothing) tm' of
        Nothing -> do
          dTy <- showMetaT $ MetaT ty'
          dTm <- bitraverse displayTypeM pure tm'
          error $ "closeType: unsolved evidence:\n\n" <> show dTm <> "\n\n" <> dTy
        Just tm'' -> pure (stripAnnots tm'', ty'')

applyEvidence
  :: (Ord tyVar, Show tyVar)
  => (tmVar -> x)
  -> [MetaT 'Check Int Ty tyVar]
  -> EvT (Tm (Meta 'Check Int tyVar)) x
  -> KindM s' (TypeM s tyVar tmVar) (EvT (Tm (Meta 'Check Int tyVar)) x)
applyEvidence _ [] !a = pure a
applyEvidence ctx (p:ps) (EvT !a) = do
  (_, EvT e) <- lift $ constructEvidence ctx p
  applyEvidence ctx ps $ EvT (TmApp a e)

funmatch ::
  (Show tyVar, Ord tyVar) =>
  (String -> Maybe (Kind Void)) -> -- ^ Type constructors
  MetaT 'Check Int Ty tyVar ->
  KindM s' (TypeM s tyVar tmVar)
    ( MetaT 'Check Int Ty tyVar
    , MetaT 'Check Int Ty tyVar
    )
funmatch tyCtorCtx (MetaT ty) =
  case ty of
    TyApp (TyApp TyArr i) o -> pure (MetaT i, MetaT o)
    _ -> do
      inTy <- lift $ TyVar <$> newMetaInf KindType
      outTy <- lift $ TyVar <$> newMetaInf KindType
      unifyType tyCtorCtx (MetaT ty) (MetaT $ tyArr inTy outTy)
      pure (MetaT inTy, MetaT outTy)

inferTypeM
  :: (Ord tyVar, Show tyVar, Show tmVar, Show x)
  => (tmVar -> x)
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (x -> Either tmVar (MetaT 'Check Int Ty tyVar))
  -> EvT (Tm (Meta 'Check Int tyVar)) x
  -> KindM s' (TypeM s tyVar tmVar)
       ( EvT (Tm (Meta 'Check Int tyVar)) x
       , MetaT 'Check Int Ty tyVar
       )
inferTypeM ctx tyCtorCtx varCtx tm =
  case unEvT tm of
    TmAnn a ty -> do
      (EvT tm', MetaT aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      instanceOf tyCtorCtx ty aTy
      pure (EvT $ TmAnn tm' ty, MetaT ty)
    TmVar P{} -> error "trying to infer type for evidence placeholder"
    TmVar (V a) -> do
      (_, tm', ty') <-
        instantiate ctx tm =<<
        either (throwError . TypeVarNotFound) pure (varCtx a)
      pure (tm', ty')
    TmApp a b -> do
      (aTm, aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a

      (_, EvT aTm', aTy') <- instantiate ctx aTm aTy
      (inTy, outTy) <- funmatch tyCtorCtx aTy'

      (EvT bTm, MetaT bTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT b

      MetaT inTy' <- lift $ findType inTy
      instanceOf tyCtorCtx inTy' bTy

      let tm' = TmApp aTm' bTm
      ty' <- lift $ findType outTy

      lift $ generalize ctx (EvT tm') ty'
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

      let tm' = TmRecord $ (\(l, EvT v, _) -> (l, v)) <$> res
      ty' <-
        lift .
        findType . MetaT $
        tyRecord $
        foldr (\(l, _, MetaT vTy) -> tyRowExtend l vTy) TyRowEmpty res

      lift $ generalize ctx (EvT tm') ty'
    TmLam s -> do
      (argTy, bodyTm, bodyTy) <- do
        argTy <- lift $ newMetaRank KindType
        ranked $ do
          (body, bodyTy) <-
            inferTypeM
              (F . ctx)
              tyCtorCtx
              (unvar (const $ Right $ MetaT $ TyVar argTy) varCtx)
              (EvT $ sequence <$> fromScope s)
          pure (argTy, body, bodyTy)

      (_, EvT bodyTm', MetaT bodyTy') <- instantiate (F . ctx) bodyTm bodyTy

      MetaT argTy' <- lift . findType $ MetaT (TyVar argTy)
      unless (isMonotype argTy') $ do
        dArgTy <- lift . displayType $ MetaT argTy'
        throwError $ TypePolymorphicArg dArgTy

      p <- lift . findType $ MetaT $ tyArr argTy' bodyTy'

      let tm' = EvT . TmLam $ toScope $ sequence <$> bodyTm'

      lift $ generalize ctx tm' p
    TmSelect l ->
      pure
        ( tm
        , MetaT $
          TyForall 2 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (tyRecord $ tyRowExtend l (pure $ B 1) (pure $ B 0)) $
          pure (B 1)
        )
    TmRestrict l ->
      pure
        ( tm
        , MetaT $
          TyForall 2 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (tyRecord $ tyRowExtend l (pure $ B 1) (pure $ B 0)) $
          tyRecord (pure $ B 0)
        )
    TmExtend l ->
      pure
        ( tm
        , MetaT $
          TyForall 2 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (pure $ B 1) $
          tyArr (tyRecord (pure $ B 0)) $
          tyRecord (tyRowExtend l (pure $ B 1) (pure $ B 0))
        )
    TmMatch l ->
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
    TmInject l ->
      pure
        ( tm
        , MetaT $
          TyForall 2 . toScope $
          tyConstraint (tyOffset l (pure $ B 0)) $
          tyArr (pure $ B 1) $
          tyVariant (tyRowExtend l (pure $ B 1) (pure $ B 0))
        )
    TmEmbed l ->
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
     , MonadIO m
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
  (=<<) (either throwError pure) .
  liftIO $
  runTypeM
    (InferState
       { _inferSupply = supply
       , _inferEvidence = mempty
       , _inferKinds =
           foldMeta
             (const Nothing)
             (const Nothing)
             (fmap (fmap absurd) . tyVarCtx)
       , _inferDepth = 0
       , _inferRank = 0
       })
    (runKindM supply $
     lift . uncurry (closeType id) =<<
     inferTypeM
       id
       tyCtorCtx
       (fmap lift . varCtx)
       (lift $ first N tm))
