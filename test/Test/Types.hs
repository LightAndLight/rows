{-# language DataKinds #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Test.Types where

import Bound.Scope (toScope)
import Bound.Var (Var(..))
import Control.Concurrent.Supply (Supply)
import Control.Lens.Review ((#))
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Class (lift)
import Data.Bitraversable (bitraverse)
import Data.IORef (newIORef)
import Data.Text (Text)
import Data.Void (Void)

import Evidence
import Inference.Kind
import Inference.State
import Inference.Type
import Inference.Type.Error
import Inference.Type.Monad
import Kind
import Label
import Meta
import Tm
import Ty

import Test.Hspec

runInferType
  :: (Ord b, Show b, Show c, MonadIO m)
  => Supply
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (b -> Maybe (Kind Void)) -- ^ Type variables
  -> (c -> Either c (Ty b)) -- ^ Term variables
  -> Tm b c
  -> m (Either (TypeError Int b c) (Tm Void c, Ty b))
runInferType supply a b c tm =
  runExceptT $ inferType supply a b c tm

runInstanceOf ::
  MonadIO m =>
  Supply ->
  InferState Int Text Text ->
  (String -> Maybe (Kind Void)) ->
  Ty (Meta 'Check Int Text) ->
  Ty (Meta 'Check Int Text) ->
  m (Either (TypeError Int Text Text) ())
runInstanceOf supply is ctx a b =
  liftIO $
  runTypeM is $
  runKindM supply $
  instanceOf ctx a b

runGeneralize ::
  MonadIO m =>
  Supply ->
  Tm (Meta 'Check Int Text) (Ev Text) ->
  Ty (Meta 'Check Int Text) ->
  m (Either
       (TypeError Int Text Text)
       (Tm (DisplayMeta Int Text) (Ev Text), Ty (DisplayMeta Int Text)))
runGeneralize supply a b =
  runExceptT $ do
    (EvT res1, MetaT res2) <-
      ExceptT $
      liftIO $
      runTypeM is $
      generalize id (EvT a) (MetaT b)
    res1' <- bitraverse (liftIO . displayMeta) pure res1
    res2' <- traverse (liftIO . displayMeta) res2
    pure (res1', res2')
  where
    is =
      InferState
      { _inferSupply = supply
      , _inferEvidence = mempty
      , _inferKinds = const Nothing
      , _inferDepth = 0
      , _inferRank = 0
      }

isInstanceOf ::
  String ->
  Supply ->
  Ty (Meta 'Check Int Text) ->
  Ty (Meta 'Check Int Text) ->
  Spec
isInstanceOf text supply t1 t2 =
  it text $ do
    let
      iState =
        InferState
        { _inferSupply = supply
        , _inferEvidence = mempty
        , _inferKinds = const Nothing
        , _inferDepth = 0
        , _inferRank = 0
        }
      ctx = const Nothing

    res <- runInstanceOf supply iState ctx t1 t2
    res `shouldBe` Right ()

notInstanceOf ::
  String ->
  Supply ->
  Ty (Meta 'Check Int Text) ->
  Ty (Meta 'Check Int Text) ->
  TypeError Int Text Text ->
  Spec
notInstanceOf text supply t1 t2 err =
  it text $ do
    let
      iState =
        InferState
        { _inferSupply = supply
        , _inferEvidence = mempty
        , _inferKinds = const Nothing
        , _inferDepth = 0
        , _inferRank = 0
        }
      ctx = const Nothing

    res <- runInstanceOf supply iState ctx t1 t2
    res `shouldBe` Left err

typesSpec :: Supply -> Spec
typesSpec supply =
  describe "Types" $ do
    describe "Generalization" $ do
      it "generalize(0, x(1) -> x(1)) ~> forall a. a -> a" $ do
        d0 <- liftIO $ newIORef 0
        r1 <- liftIO $ newIORef (Rank 1)
        res <-
          runGeneralize
            supply
            (lam (V "x") $ pure (V "x"))
            (tyArr (pure $ M d0 r1 0) (pure $ M d0 r1 0))

        res `shouldBe`
          Right
          ( lam (V "x") $ pure (V "x")
          , forall_ [_N # "a"] $ tyArr (_N # "a") (_N # "a")
          )
      it "generalize(0, x(inf) -> x(inf)) ~> forall a. a -> a" $ do
        d0 <- liftIO $ newIORef 0
        inf <- liftIO $ newIORef Inf
        res <-
          runGeneralize
            supply
            (lam (V "x") $ pure (V "x"))
            (tyArr (_M # (d0, inf, 0)) (_M # (d0, inf, 0)))

        res `shouldBe`
          Right
          ( lam (V "x") $ pure (V "x")
          , forall_ [_N # "a"] $
            tyArr (_N # "a") (_N # "a")
          )

    describe "Subsumption" $ do
      isInstanceOf
        "1) |- Int -> Int `instanceOf` forall a. a -> a"
        supply
        (tyArr TyInt TyInt)
        (forall_ [N "a"] (tyArr (pure $ N "a") (pure $ N "a")))
      notInstanceOf
        "2) |- forall a. a -> a `notInstanceOf` Int -> Int"
        supply
        (forall_ [N "a"] (tyArr (pure $ N "a") (pure $ N "a")))
        (tyArr TyInt TyInt)
        (TypeMismatch (liftDM $ S 1 0) (lift TyInt))
      isInstanceOf
        "3) |- forall b. (forall a. a -> b) -> (forall a. -> b) `instanceOf` forall a. a -> a"
        supply
        (forall_ [N "b"] $
         tyArr
           (forall_ [N "a"] $ tyArr (pure $ N "a") (pure $ N "b"))
           (forall_ [N "a"] $ tyArr (pure $ N "a") (pure $ N "b")))
        (forall_ [N "a"] (tyArr (pure $ N "a") (pure $ N "a")))
      it "4) |- forall a. a -> b `notInstanceOf` forall a. a -> a" $ do
        let
          iState =
            InferState
            { _inferSupply = supply
            , _inferEvidence = mempty
            , _inferKinds =
              \case
                M _ _ 99 -> Just KindType
                _ -> Nothing
            , _inferDepth = 0
            , _inferRank = 0
            }
          ctx = const Nothing

        inf <- liftIO $ newIORef Inf
        d0 <- liftIO $ newIORef 0

        res <-
          runInstanceOf supply iState ctx
            (forall_ [N "a"] $ tyArr (pure $ N "a") (pure $ M d0 inf 99))
            (forall_ [N "a"] $ tyArr (pure $ N "a") (pure $ N "a"))

        res `shouldBe` Left (TypeEscaped [liftDM $ S 1 0])
      isInstanceOf
        "5) |- forall a. (l | {}) => a `instanceOf` forall a. a"
        supply
        (forall_ [N "a"] $
         tyConstraint (tyOffset (Label "l") TyRowEmpty) $
         pure (N "a"))
        (forall_ [N "a"] $
         pure (N "a"))

    it "1) |- (\\x -> x) : forall a. a -> a" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        TmLam (toScope $ TmVar (B ()))

      res `shouldBe`
        Right
        ( lam "x" $ pure "x"
        , TyForall 1 $ toScope $
          tyArr (TyVar $ B 0) (TyVar $ B 0)
        )

    it "2) |- (\\x y -> x) : forall a b. a -> b -> a" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        TmLam (toScope (TmLam (toScope $ TmVar (F (B ())))))

      res `shouldBe`
        Right
          ( lam "x" $ lam "y" $ pure "x"
          , TyForall 2 $ toScope $
            tyArr (TyVar (B 0)) $
            tyArr (TyVar (B 1)) $
            TyVar (B 0)
          )

    it "3) (\\x -> x x) occurs error" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      res <-
        runInferType
          supply
          tyCtorCtx
          tyVarCtx
          varCtx
          (TmLam $ toScope $ TmApp (TmVar (B ())) (TmVar (B ())))

      res `shouldBe`
        Left
        (TypeOccurs 1 . DisplayMetaT $
         tyArr (_M # (0, Rank 0, 1)) (_M # (0, Rank 0, 2)))

    it "4) f : X -> Y, x : Z |/- f x : Y" $ do
      let
        tyCtorCtx x =
          case x of
            "X" -> Just KindType
            "Y" -> Just KindType
            "Z" -> Just KindType
            _ -> Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x =
          case x of
            "f" -> Right $ TyApp (TyApp TyArr (TyCtor "X")) (TyCtor "Y")
            "x" -> Right $ TyCtor "Z"
            _ -> Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        TmApp (TmVar "f") (TmVar "x")

      res `shouldBe`
        Left (TypeMismatch (lift $ TyCtor "X") (lift $ TyCtor "Z"))

    it "5) |- _.l : forall r a. (l | r) => Record (l : a | r) -> a" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      res <- runInferType supply tyCtorCtx tyVarCtx varCtx (TmSelect $ Label "l")

      res `shouldBe`
        Right
          ( TmSelect (Label "l")
          , forall_ ["r", "a"] $
            tyConstraint (tyOffset (Label "l") (pure "r")) $
            tyArr
              (tyRecord $ tyRowExtend (Label "l") (pure "a") (pure "r"))
              (pure "a")
          )

    it "6) |- (\\r -> r.f r.x) : forall a r b. (f | r) => (x | r) => Record (f : a -> b, x : a | r) -> b" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        lam "r"
          (TmApp
             (tmSelect (pure "r") (Label "f"))
             (tmSelect (pure "r") (Label "x")))

      res `shouldBe`
        Right
          ( lam "offset1" $ lam "offset2" $
            lam "r" $
            TmApp
              (TmApp (TmApp (TmSelect $ Label "f") (pure "offset1")) (pure "r"))
              (TmApp (TmApp (TmSelect $ Label "x") (TmAdd (TmInt 1) (pure "offset2"))) (pure "r"))
          , forall_ ["r", "a", "b"] $
            tyConstraint
              (tyOffset (Label "f") (pure "r")) $
            tyConstraint
              (tyOffset (Label "x") (pure "r")) $
            tyArr
              (tyRecord $
                tyRowExtend (Label "f") (tyArr (pure "a") (pure "b")) $
                tyRowExtend (Label "x") (pure "a") $
                (pure "r"))
              (pure "b")
          )

    it "7) r : Record (x : A, y : B) |- _.l 1 r : B" $ do
      let
        tyCtorCtx x =
          case x of
            "A" -> Just KindType
            "B" -> Just KindType
            _ -> Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x =
          case x of
            "r" ->
              Right $
              tyRecord $
              tyRowExtend (Label "x") (TyCtor "A") $
              tyRowExtend (Label "y") (TyCtor "B") $
              TyRowEmpty
            _ -> Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        tmSelect (pure "r") (Label "y")

      res `shouldBe`
        Right
        ( TmApp (TmApp (TmSelect $ Label "y") (TmAdd (TmInt 1) (TmInt 0))) (pure "r")
        , forall_ [] $ TyCtor "B"
        )

    it "8) r : Row, x : Record (x : A | r) -> A, y : Record (y : A | r) |/- x y : A" $ do
      let
        tyCtorCtx x =
          case x of
            "A" -> Just KindType
            _ -> Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx x =
          case x of
            "r" -> Just KindRow
            _ -> Nothing

        varCtx :: String -> Either String (Ty String)
        varCtx x =
          case x of
            "x" ->
              Right $
              tyArr
                (tyRecord $ tyRowExtend (Label "x") (TyCtor "A") $ pure "r")
                (TyCtor "A")
            "y" ->
              Right $
              tyRecord $ tyRowExtend (Label "y") (TyCtor "A") $ pure "r"
            _ -> Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        TmApp (pure "x") (pure "y")

      res `shouldBe`
        Left
        (TypeMismatch
            (lift $ tyRowExtend (Label "x") (TyCtor "A") $ pure "r")
            (lift $ tyRowExtend (Label "y") (TyCtor "A") $ pure "r"))

    it "9) r : Row, x : Record (x : A, y : B | r) -> A, y : Record (y : A, X : B | r) |/- x y : A" $ do
      let
        tyCtorCtx x =
          case x of
            "A" -> Just KindType
            "B" -> Just KindType
            _ -> Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx x =
          case x of
            "r" -> Just KindRow
            _ -> Nothing

        varCtx :: String -> Either String (Ty String)
        varCtx x =
          case x of
            "x" ->
              Right $
              tyArr
                (tyRecord $
                  tyRowExtend (Label "x") (TyCtor "A") $
                  tyRowExtend (Label "y") (TyCtor "B") $
                  pure "r")
                (TyCtor "A")
            "y" ->
              Right $
              tyRecord $
              tyRowExtend (Label "y") (TyCtor "A") $
              tyRowExtend (Label "x") (TyCtor "B") $
              pure "r"
            _ -> Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        TmApp (pure "x") (pure "y")

      res `shouldBe`
        Left
        (TypeMismatch
            (lift $ TyCtor "A")
            (lift $ TyCtor "B"))

    it "10) r : Record (x : A, y : B) |- _.x 0 r : A" $ do
      let
        tyCtorCtx x =
          case x of
            "A" -> Just KindType
            "B" -> Just KindType
            _ -> Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x =
          case x of
            "r" ->
              Right $
              tyRecord $
              tyRowExtend (Label "x") (TyCtor "A") $
              tyRowExtend (Label "y") (TyCtor "B") $
              TyRowEmpty
            _ -> Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        tmSelect (pure "r") (Label "x")

      res `shouldBe`
        Right
        ( TmApp (TmApp (TmSelect $ Label "x") (TmInt 0)) (pure "r")
        , forall_ [] $ TyCtor "A"
        )

    it "11) |- (\\r -> r.f r.x) *{ f = \\x -> x, 99 } : Int" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        TmApp
           (lam "r" $
           TmApp
             (tmSelect (pure "r") (Label "f"))
             (tmSelect (pure "r") (Label "x")))
           (TmRecord
            [ (Label "f", lam "x" $ pure "x")
            , (Label "x", TmInt 99)
            ])

      res `shouldBe`
        Right
          ( TmApp
              (lam "r" $
                TmApp
                  (TmApp (TmApp (TmSelect $ Label "f") (TmInt 0)) (pure "r"))
                  (TmApp (TmApp (TmSelect $ Label "x") (TmAdd (TmInt 1) (TmInt 0))) (pure "r")))
              (TmApp (TmApp (TmApp (TmExtend $ Label "f") (TmInt 0)) (lam "x" $ pure "x")) $
                TmApp (TmApp (TmApp (TmExtend $ Label "x") (TmInt 0)) (TmInt 99)) $
                (TmRecord []))
          , forall_ [] TyInt
          )

    it "12) +{ x = 99 } 0 : Variant (x : Int, y : Int)" $ do
      let
        tyCtorCtx _ = Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

        ty =
          tyVariant $
          tyRowExtend (Label "x") TyInt $
          tyRowExtend (Label "y") TyInt $
          TyRowEmpty

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        tmInject (Label "x") (TmInt 99) `TmAnn` ty

      res `shouldBe`
        Right
        ( TmApp (TmApp (TmInject $ Label "x") (TmInt 0)) (TmInt 99)
        , forall_ [] ty
        )

    it "13) +{ y = 99 } (1 + 0) : Variant (x : Int, y : Int)" $ do
      let
        tyCtorCtx _ = Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

        ty =
          tyVariant $
          tyRowExtend (Label "x") TyInt $
          tyRowExtend (Label "y") TyInt $
          TyRowEmpty

      res <-
        runInferType supply tyCtorCtx tyVarCtx varCtx $
        tmInject (Label "y") (TmInt 99) `TmAnn` ty

      res `shouldBe`
        Right
        ( TmApp (TmApp (TmInject $ Label "y") (TmAdd (TmInt 1) (TmInt 0))) (TmInt 99)
        , forall_ [] ty
        )
