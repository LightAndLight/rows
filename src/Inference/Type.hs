{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses #-}
{-# language OverloadedLists #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language RankNTypes #-}
module Inference.Type where

import Bound.Scope (abstract, abstractEither, fromScope, toScope)
import Bound.Var (Var(..), unvar)
import Control.Applicative ((<|>))
import Control.Concurrent.Supply (Supply, freshId)
import Control.Lens.Getter (use, uses)
import Control.Lens.TH (makeClassyPrisms, makeLenses)
import Control.Lens.Plated (plate)
import Control.Lens.Review ((#))
import Control.Lens.Setter ((%=), (.=))
import Control.Lens.Traversal (traverseOf)
import Control.Lens.Wrapped (_Wrapped, _Unwrapped)
import Control.Monad ((<=<))
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (MonadState, State, runState, evalStateT, modify)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Strict (WriterT, runWriterT, tell)
import Data.Bifunctor (first)
import Data.Either (partitionEithers)
import Data.Equivalence.Monad (MonadEquiv, equate, classDesc, runEquivT)
import Data.Foldable (toList)
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.Sequence ((|>), Seq)
import Data.Traversable (for)
import Data.Void (Void, absurd)

import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import Evidence
import Inference.Kind
import Kind
import Label
import Meta
import Tm
import Ty

data EvEntry a b c
  = EvEntry c (MetaT a Ty b)

data InferState a b c
  = InferState
  { _inferSupply :: Supply
  , _inferEvidence :: Seq (EvEntry a b c)
  , _inferKinds :: Meta a b -> Maybe (Kind Void)
  }
makeLenses ''InferState

newEv :: MonadState (InferState a b Int) m => MetaT a Ty b -> m (Ev Int x)
newEv ty = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferEvidence %= (|> EvEntry v ty)
  pure $ E v

newMeta :: MonadState (InferState Int b c) m => Kind Void -> m (Meta Int b)
newMeta kind = do
  (v, supply') <- uses inferSupply freshId
  inferSupply .= supply'
  inferKinds %=
    \f x ->
      f x <|>
      foldMeta (\y -> if y == v then Just kind else Nothing) (const Nothing) x
  pure $ M v

data TypeError a b c
  = TypeOccurs a (MetaT a Ty b)
  | TypeMismatch (MetaT a Ty b) (MetaT a Ty b)
  | TypeVarNotFound c
  | TypeKindMismatch (MetaT a Ty b) (Kind Void) (MetaT a Ty b) (Kind Void)
  | TypeCannotDeduce (MetaT a Ty b)
  | TypeKindError (KindError (Meta Int b))
  deriving (Eq, Show)
makeClassyPrisms ''TypeError

instance AsKindError (TypeError a b c) (Meta Int b) where
  _KindError = _TypeKindError

occursType :: Eq meta => meta -> MetaT meta Ty a -> Bool
occursType v =
  foldr
    (\a b -> foldMeta (== v) (const False) a || b)
    False .
    unMetaT

rowTail :: Show a => Ty (Meta Int a) -> Ty (Meta Int a)
rowTail (TyApp (TyApp TyRowExtend{} _) r) = r
rowTail (TyVar v) = TyVar v
rowTail TyRowEmpty = TyRowEmpty
rowTail a = error $ "rowTail: can't get tail of:\n\n" <> show a

rewriteRow
  :: ( MonadError (TypeError Int tyVar tmVar) m
     , MonadState (InferState Int tyVar ev) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar, Show tyVar
     )
  => (String -> Maybe (Kind Void))
  -> Ty (Meta Int tyVar) -- ^ row tail
  -> Label -- ^ desired label
  -> Ty (Meta Int tyVar) -- ^ term to rewrite
  -> m (Maybe (Label, Ty (Meta Int tyVar), Ty (Meta Int tyVar)))
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
        metaTy <- TyVar <$> newMeta KindType
        metaRow <- TyVar <$> newMeta KindRow
        equate (MetaT ty) (MetaT $ tyRowExtend ll metaTy metaRow)
        pure $ Just (ll, metaTy, metaRow)
    _ -> pure Nothing

combineType
  :: (Show a, Show b, Ord a, Eq b)
  => MetaT a Ty b
  -> MetaT a Ty b
  -> MetaT a Ty b
combineType (MetaT x) (MetaT y) = MetaT $ go x y
  where
    go TyArr TyArr = TyArr
    go TyRowEmpty TyRowEmpty = TyRowEmpty
    go TyRecord TyRecord = TyRecord
    go TyVariant TyVariant = TyVariant
    go (TyRowExtend l) (TyRowExtend l') | l == l' = TyRowExtend l
    go (TyCtor s) (TyCtor s') | s == s' = TyCtor s
    go (TyVar (N a)) (TyVar (N b)) | a == b = TyVar (N b)
    go (TyVar (M a)) (TyVar (M b)) = TyVar $ M (min a b)
    go (TyApp a b) (TyApp a' b') = TyApp (go a a') (go b b')
    go (TyVar M{}) b = b
    go a (TyVar M{}) = a
    go _ _ =
      error $
      "combineType: combining un-unifiable terms\n\n" <>
      show x <>
      "\n\n" <>
      show y

unifyType
  :: forall tmVar tyVar ev c m
   . ( MonadError (TypeError Int tyVar tmVar) m
     , MonadState (InferState Int tyVar ev) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar, Show tyVar
     )
  => (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> MetaT Int Ty tyVar
  -> MetaT Int Ty tyVar
  -> m ()
unifyType tyCtorCtx x y = do
  supply <- use inferSupply
  tyVarCtx <- use inferKinds
  x' <- unMetaT <$> findType x
  y' <- unMetaT <$> findType y
  xKind <- evalStateT (inferKind tyCtorCtx tyVarCtx x') supply
  yKind <- evalStateT (inferKind tyCtorCtx tyVarCtx y') supply
  if xKind == yKind
    then go x' y'
    else throwError $ _TypeKindMismatch # (MetaT x', absurd <$> xKind, MetaT y', absurd <$> yKind)
  where
    go :: Ty (Meta Int tyVar) -> Ty (Meta Int tyVar) -> m ()
    go TyArr TyArr = pure ()
    go TyRowEmpty TyRowEmpty = pure ()
    go TyRecord TyRecord = pure ()
    go TyVariant TyVariant = pure ()
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
    go ty@(TyVar M{}) ty'@(TyVar M{}) = equate (MetaT ty) (MetaT ty')
    go (TyApp a b) (TyApp a' b') =
      unifyType tyCtorCtx (MetaT a) (MetaT a') *>
      unifyType tyCtorCtx (MetaT b) (MetaT b')
    go ty'@(TyVar (M a)) ty =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else equate (MetaT ty') (MetaT ty)
    go ty ty'@(TyVar (M a)) =
      if occursType a $ MetaT ty
      then throwError $ TypeOccurs a (MetaT ty)
      else equate (MetaT ty) (MetaT ty')
    go l m = throwError $ TypeMismatch (MetaT l) (MetaT m)

findType
  :: MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
  => MetaT Int Ty tyVar
  -> m (MetaT Int Ty tyVar)
findType = _Wrapped go
  where
    go = traverseOf plate go <=< _Unwrapped classDesc

generalize :: MetaT Int Ty tyVar -> Forall tyVar
generalize (MetaT t) =
  Forall (Set.size uniq) $
  abstractEither
    (foldMeta (Left . fromJust . (`elemIndex` ordered uniq metas)) Right)
    t
  where
    ordered set xs =
      case xs of
        [] -> []
        a:as ->
          if a `Set.member` set
          then a : ordered (Set.delete a set) as
          else ordered set as

    (uniq, metas) =
      foldr
        (\a (b1, b2) -> foldMeta ((,) <$> (`Set.insert` b1) <*> (: b2)) (const (b1, b2)) a)
        (Set.empty, [])
        t

stripAnnots :: Tm tyVar tmVar -> Tm Void tmVar
stripAnnots tm =
  case tm of
    TmAnn a _ -> stripAnnots a
    TmVar a -> TmVar a
    TmApp a b -> TmApp (stripAnnots a) (stripAnnots b)
    TmAdd a b -> TmAdd (stripAnnots a) (stripAnnots b)
    TmLam s -> TmLam . toScope . stripAnnots $ fromScope s
    TmEmpty -> TmEmpty
    TmExtend l -> TmExtend l
    TmSelect l -> TmSelect l
    TmRestrict l -> TmRestrict l
    TmMatch l -> TmMatch l
    TmInject l -> TmInject l
    TmEmbed l -> TmEmbed l
    TmInt n -> TmInt n

evidenceFor
  :: ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Show tyVar
     )
  => MetaT Int Ty tyVar
  -> WriterT
       (Seq (EvEntry Int tyVar Int))
       m
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
  :: forall tyVar tmVar c m x
   . ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Show tyVar
     )
  => m
       ( [(Int, EvT Int (Tm (Meta Int tyVar)) x)]
       , [(Int, MetaT Int Ty tyVar)]
       )
getEvidence = use inferEvidence >>= go
  where
    go
      :: Seq (EvEntry Int tyVar Int)
      -> m
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
  :: forall tyVar tmVar c x m
   . ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar
     , Show tyVar, Show tmVar
     , Show x
     )
  => Tm (Meta Int tyVar) (Ev Int x)
  -> m (Tm (Meta Int tyVar) x, [MetaT Int Ty tyVar])
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

generalizeType
  :: forall tyVar tmVar c x m
   . ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Eq tyVar
     , Show tyVar, Show tmVar
     , Show x
     )
  => (EvT Int (Tm (Meta Int tyVar)) x, MetaT Int Ty tyVar)
  -> m (Tm Void x, Forall tyVar)
generalizeType (EvT tm, MetaT ty) = do
  (tm', constraints) <- finalizeEvidence tm
  ty' <-
    generalize <$>
    findType (MetaT $ foldr (tyConstraint . unMetaT) ty constraints)
  pure (stripAnnots tm', ty')

stripConstraints
  :: forall a b
   . MetaT b Ty a
  -> (MetaT b Ty a, [MetaT b Ty a])
stripConstraints =
  flip runState mempty . _Wrapped go
  where
    go
      :: Ty (Meta b a)
      -> State [MetaT b Ty a] (Ty (Meta b a))
    go ty =
      -- if we introduce first-class polymorphism, then we can't float
      -- constraints from under a forall
      case ty of
        TyApp (TyApp TyConstraint c) rest -> do
          modify $ (MetaT c :)
          go rest
        TyApp{} -> pure ty
        TyArr -> pure ty
        TyCtor{} -> pure ty
        TyVar{} -> pure ty
        TyRowEmpty -> pure ty
        TyRowExtend{} -> pure ty
        TyRecord -> pure ty
        TyVariant -> pure ty
        TyOffset{} -> pure ty
        TyConstraint -> pure ty
        TyInt -> pure ty

applyEvidence
  :: ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Show tyVar, Show x
     )
  => [MetaT Int Ty tyVar]
  -> EvT Int (Tm (Meta Int tyVar)) x
  -> m (EvT Int (Tm (Meta Int tyVar)) x)
applyEvidence [] !a = pure a
applyEvidence (p:ps) (EvT !a) = do
  res <- fmap fst . runWriterT $ evidenceFor p
  EvT e <- maybe (EvT . TmVar <$> newEv p) pure res
  applyEvidence ps $ EvT (TmApp a e)

inferTypeM
  :: ( MonadState (InferState Int tyVar Int) m
     , MonadError (TypeError Int tyVar tmVar) m
     , MonadEquiv c (MetaT Int Ty tyVar) (MetaT Int Ty tyVar) m
     , Ord tyVar, Show tyVar, Show x
     )
  => (tmVar -> x)
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (x -> Either tmVar (MetaT Int Ty tyVar))
  -> EvT Int (Tm (Meta Int tyVar)) x
  -> m (EvT Int (Tm (Meta Int tyVar)) x, MetaT Int Ty tyVar)
inferTypeM ctx tyCtorCtx varCtx tm =
  case unEvT tm of
    TmAnn a ty -> do
      (EvT tm', aTy) <- inferTypeM ctx tyCtorCtx varCtx $ EvT a
      unifyType tyCtorCtx aTy (MetaT ty)
      pure (EvT $ TmAnn tm' ty, MetaT ty)
    TmVar E{} -> error "trying to infer type for evidence variable"
    TmVar (V a) -> do
      ty <- either (throwError . TypeVarNotFound) pure $ varCtx a
      let (ty', constraints) = stripConstraints ty
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
    TmLam s -> do
      argTy <- newMeta KindType
      (EvT body', bodyTy) <-
        inferTypeM
          (F . ctx)
          tyCtorCtx
          (unvar (const $ Right $ MetaT $ TyVar argTy) varCtx)
          (EvT $ sequence <$> fromScope s)
      pure
        ( EvT $ TmLam $ toScope $ sequence <$> body'
        , MetaT $ TyApp (TyApp TyArr (TyVar argTy)) (unMetaT bodyTy)
        )
    TmEmpty -> pure (EvT TmEmpty, lift $ tyRecord TyRowEmpty)
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
  -> m (Tm Void tmVar, Forall tyVar)
inferType supply tyCtorCtx tyVarCtx varCtx tm =
  runEquivT
    id
    combineType
    (evalStateT
       (generalizeType =<<
        inferTypeM
          id
          tyCtorCtx
          (fmap lift . varCtx)
          (lift $ first N tm))
       (InferState
        { _inferSupply = supply
        , _inferEvidence = mempty
        , _inferKinds = foldMeta (const Nothing) tyVarCtx
        }))
