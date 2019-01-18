{-# language FunctionalDependencies, MultiParamTypeClasses #-}
{-# language ScopedTypeVariables #-}
module Optimisation where

import Bound.Scope (fromScope, toScope, instantiate1)
import Bound.Var (Var(..), unvar, _F)
import Control.Lens.Fold (preview)
import Control.Lens.Getter (uses)
import Control.Lens.Lens (Lens')
import Control.Monad.State (MonadState)
import Data.Bifunctor (first)
import Data.Set (Set)

import qualified Data.Set as Set

import Tm

class HasRecBinders s a | s -> a where
  recBinders :: Lens' s (Set a)

{-

everything in the binding context is inlined, unless is considered a recursive
bindings

-}
inline
  :: forall ty a s m
   . ( Ord a
     , HasRecBinders s a
     , MonadState s m
     )
  => (a -> Tm ty a) -- ^ Bindings
  -> Tm ty a -- ^ Input term
  -> m (Tm ty a)
inline binds = go id Right
  where
    go
      :: forall x
       . (a -> x)
      -> (x -> Either x a)
      -> Tm ty x -- ^ Input term
      -> m (Tm ty x)
    go ctx toVar tm =
      case tm of
        TmVar a ->
          case toVar a of
            Left{} -> pure $ TmVar a
            Right x -> do
              isRec <- uses recBinders $ Set.member x
              if isRec
                then pure $ TmVar a
                else pure $ ctx <$> binds x
        TmAnn a b -> (\a' -> TmAnn a' b) <$> go ctx toVar a
        TmApp a b -> TmApp <$> go ctx toVar a <*> go ctx toVar b
        TmLam s ->
          TmLam . toScope <$>
          go (F . ctx) (unvar (Left . B) (first F . toVar)) (fromScope s)
        TmEmpty -> pure TmEmpty
        TmExtend l -> pure $ TmExtend l
        TmSelect l -> pure $ TmSelect l
        TmRestrict l -> pure $ TmRestrict l
        TmMatch l -> pure $ TmMatch l
        TmInject l -> pure $ TmInject l
        TmEmbed l -> pure $ TmEmbed l

-- |
-- @\\x -> f x ~~> f   when   notFreeIn(x, f)@
etaReduce :: Tm ty a -> Maybe (Tm ty a)
etaReduce (TmLam s) =
  case fromScope s of
    TmApp f (TmVar (B ())) -> traverse (preview _F) f
    _ -> Nothing
etaReduce _ = Nothing

-- |
-- @(\\x. y) a ~~> y[a]@
betaReduce :: Tm ty a -> Maybe (Tm ty a)
betaReduce tm =
  case tm of
    TmApp (TmLam s) x -> Just $ instantiate1 x s
    _ -> Nothing

-- |
-- @*{x_1 = v_1, x_2 = v_2, ..., x_i = v_i, ... | ... }.x_i ~~> v_i@
recordElim :: Tm ty a -> Maybe (Tm ty a)
recordElim tm =
  case tm of
    TmApp (TmSelect l) r -> selectFrom l r
    _ -> Nothing

-- |
-- @
-- +{ +{ x_i = v_i } is x_1 ? v_1 | \\r_1 ->
--    +{ r_1 is x_2 ? v_2         | \\r_2 ->
--    +{ ...                      | \\r_i-1 ->
--    +{ r_i-1 is x_i ? v_i       | \\r_i ->
--    +{ ... }}}}
--  }
--
-- ~~>
--
-- v_i
-- @
variantElim :: Tm ty a -> Maybe (Tm ty a)
variantElim tm =
  case tm of
    TmApp (TmApp (TmApp (TmMatch l) (TmApp (TmInject l') a)) fVal) rest ->
      if l == l'
      then Just $ TmApp fVal a
      else
        case rest of
          TmLam fRest -> variantElim $ instantiate1 (tmInject l' a) fRest
          _ -> Just $ TmApp rest (tmInject l' a)
    _ -> Nothing
