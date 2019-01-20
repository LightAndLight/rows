{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Test.Kinds where

import Control.Concurrent.Supply (Supply)
import Control.Monad.Except (runExcept)
import Control.Monad.State (evalStateT)
import Data.Void (Void)

import Inference.Kind
import Inference.Kind.Error
import Kind
import Label
import Ty

import Test.Hspec

runInferKind
  :: Supply
  -> (String -> Maybe (Kind Void)) -- ^ Constructors
  -> (a -> Maybe (Kind Void)) -- ^ Variables
  -> Ty a
  -> Either (KindError a) (Kind Void)
runInferKind supply a b ty =
  runExcept $ evalStateT (inferKind a b ty) supply

runInferDataDeclKind
  :: Eq a
  => Supply
  -> (String -> Maybe (Kind Void)) -- ^ Constructors
  -> (a -> Maybe (Kind Void)) -- ^ Variables
  -> (String, [a]) -- ^ Type constructor and arguments
  -> [[Ty a]] -- ^ Fields for each data constructor
  -> Either (KindError a) (Kind Void)
runInferDataDeclKind supply a b c d =
  runExcept $ evalStateT (inferDataDeclKind a b c d) supply

kindsSpec :: Supply -> Spec
kindsSpec supply =
  describe "Kinds" $ do
    it "1) A : Type -> Row, B : Type |- a b : Row" $ do
      let
        ctorCtx =
          \case
            "A" -> Just $ KindArr KindType KindRow
            "B" -> Just KindType
            _ -> Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

      runInferKind supply ctorCtx varCtx (TyApp (TyCtor "A") (TyCtor "B"))
        `shouldBe`
        Right KindRow

    it "2) A : Type, B : Row |- { l : A | B } : Row" $ do
      let
        ctorCtx =
          \case
            "A" -> Just KindType
            "B" -> Just KindRow
            _ -> Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

      runInferKind
        supply
        ctorCtx
        varCtx
        (tyRowExtend (Label "l") (TyCtor "A") (TyCtor "B"))
        `shouldBe`
        Right KindRow

    it "3) A : Type -> Row, B : Row |/- a b : Row" $ do
      let
        ctorCtx =
          \case
            "A" -> Just $ KindArr KindType KindRow
            "B" -> Just KindRow
            _ -> Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

      runInferKind supply ctorCtx varCtx (TyApp (TyCtor "A") (TyCtor "B"))
        `shouldBe`
        Left (KindMismatch KindType KindRow)

    it "4) Mu : ?0 -> Type, f : ?0, f (Mu f) : Type |- Mu : (Type -> Type) -> Type" $ do
      let
        ctorCtx = const Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

        ctorArgs = ("Mu", ["f"])
        branches = [[TyApp (TyVar "f") (TyApp (TyCtor "Mu") (TyVar "f"))]]

      runInferDataDeclKind
        supply
        ctorCtx
        varCtx
        ctorArgs
        branches

        `shouldBe`

        Right (KindArr (KindArr KindType KindType) KindType)

    it "5) Mu : ?0 -> Type, f : ?0, f f : Type |- occurs error" $ do
      let
        ctorCtx = const Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

        ctorArgs = ("Mu", ["f"])
        branches = [[TyApp (TyVar "f") (TyVar "f")]]

      runInferDataDeclKind
        supply
        ctorCtx
        varCtx
        ctorArgs
        branches

        `shouldBe`

        Left (KindOccurs 0 (KindArr (KindVar 0) (KindVar 1)))
