{-# language OverloadedStrings #-}
module Test.Types where

import Bound.Scope (toScope)
import Bound.Var (Var(..))
import Control.Concurrent.Supply (Supply)
import Control.Monad.Except (runExcept)
import Control.Monad.Trans.Class (lift)
import Data.Void (Void)

import Inference.Type
import Inference.Type.Error
import Kind
import Label
import Meta
import Tm
import Ty

import Test.Hspec

runInferType
  :: (Ord b, Show b, Show c)
  => Supply
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (b -> Maybe (Kind Void)) -- ^ Type variables
  -> (c -> Either c (Ty b)) -- ^ Term variables
  -> Tm b c
  -> Either (TypeError Int b c) (Tm Void c, Forall b)
runInferType supply a b c tm =
  runExcept $ inferType supply a b c tm

typesSpec :: Supply -> Spec
typesSpec supply =
  describe "Types" $ do
    it "1) |- (\\x -> x) : forall a. a -> a" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (TmLam $ toScope $ TmVar (B ()))

        `shouldBe`

        Right
        ( lam "x" $ pure "x"
        , Forall 1 $ toScope $
          tyArr (TyVar $ B 0) (TyVar $ B 0)
        )

    it "2) |- (\\x y -> x) : forall a b. a -> b -> a" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (TmLam $ toScope $ TmLam $ toScope $ TmVar (F (B ())))

        `shouldBe`

        Right
          ( lam "x" $ lam "y" $ pure "x"
          , Forall 2 $ toScope $
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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (TmLam $ toScope $ TmApp (TmVar (B ())) (TmVar (B ())))

        `shouldBe`

        Left (TypeOccurs 0 (MetaT $ TyApp (TyApp TyArr (TyVar (M 0))) (TyVar (M 1))))

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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (TmApp (TmVar "f") (TmVar "x"))

        `shouldBe`

        Left (TypeMismatch (lift $ TyCtor "X") (lift $ TyCtor "Z"))

    it "5) |- _.l : forall r a. (l | r) => Record (l : a | r) -> a" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (TmSelect $ Label "l")

        `shouldBe`

        Right
          ( lam "offset" $ TmApp (TmSelect $ Label "l") (pure "offset")
          , forAll ["r", "a"] $
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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (lam "r" $
          TmApp
            (tmSelect (pure "r") (Label "f"))
            (tmSelect (pure "r") (Label "x")))

        `shouldBe`

        Right
          ( lam "offset1" $ lam "offset2" $
            lam "r" $
            TmApp
              (TmApp (TmApp (TmSelect $ Label "f") (pure "offset1")) (pure "r"))
              (TmApp (TmApp (TmSelect $ Label "x") (TmAdd (TmInt 1) (pure "offset2"))) (pure "r"))
          , forAll ["r", "a", "b"] $
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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (tmSelect (pure "r") (Label "y"))

        `shouldBe`

        Right
        ( TmApp (TmApp (TmSelect $ Label "y") (TmAdd (TmInt 1) (TmInt 0))) (pure "r")
        , forAll [] $ TyCtor "B"
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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (TmApp (pure "x") (pure "y"))

        `shouldBe`

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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (TmApp (pure "x") (pure "y"))

        `shouldBe`

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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (tmSelect (pure "r") (Label "x"))

        `shouldBe`

        Right
        ( TmApp (TmApp (TmSelect $ Label "x") (TmInt 0)) (pure "r")
        , forAll [] $ TyCtor "A"
        )

    it "11) |- (\\r -> r.f r.x) *{ f = \\x -> x, 99 } : Int" $ do
      let
        tyCtorCtx = const Nothing

        tyVarCtx :: String -> Maybe (Kind Void)
        tyVarCtx = const Nothing

        varCtx :: String -> Either String (Ty tyVar)
        varCtx x = Left x

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (TmApp
            (lam "r" $
            TmApp
              (tmSelect (pure "r") (Label "f"))
              (tmSelect (pure "r") (Label "x")))
            (tmExtend (Label "f") (lam "x" $ pure "x") $
            tmExtend (Label "x") (TmInt 99) $
            (TmRecord [])))

        `shouldBe`

        Right
          ( TmApp
              (lam "r" $
                TmApp
                  (TmApp (TmApp (TmSelect $ Label "f") (TmInt 0)) (pure "r"))
                  (TmApp (TmApp (TmSelect $ Label "x") (TmAdd (TmInt 1) (TmInt 0))) (pure "r")))
              (TmApp (TmApp (TmApp (TmExtend $ Label "f") (TmInt 0)) (lam "x" $ pure "x")) $
                TmApp (TmApp (TmApp (TmExtend $ Label "x") (TmInt 0)) (TmInt 99)) $
                (TmRecord []))
          , forAll [] TyInt
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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (tmInject (Label "x") (TmInt 99) `TmAnn` ty)

        `shouldBe`

        Right
        ( TmApp (TmApp (TmInject $ Label "x") (TmInt 0)) (TmInt 99)
        , forAll [] ty
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

      runInferType
        supply
        tyCtorCtx
        tyVarCtx
        varCtx
        (tmInject (Label "y") (TmInt 99) `TmAnn` ty)

        `shouldBe`

        Right
        ( TmApp (TmApp (TmInject $ Label "y") (TmAdd (TmInt 1) (TmInt 0))) (TmInt 99)
        , forAll [] ty
        )
