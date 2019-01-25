{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Test.Kinds where

import Control.Concurrent.Supply (Supply)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO)
import Data.Void (Void)

import Inference.Kind
import Inference.Kind.Error
import Kind
import Label
import Ty

import Test.Hspec

runInferKind
  :: MonadIO m
  => Supply
  -> (x -> ExceptT (KindError a) m a) -- ^ Freeze variables
  -> (String -> Maybe (Kind Void)) -- ^ Constructors
  -> (x -> Maybe (Kind Void)) -- ^ Variables
  -> Ty x
  -> m (Either (KindError a) (Kind Void))
runInferKind supply freezeVars a b ty =
  runExceptT $ inferKind supply freezeVars a b ty

runInferDataDeclKind
  :: (Eq x, MonadIO m)
  => Supply
  -> (x -> ExceptT (KindError a) m a) -- ^ Freeze variables
  -> (String -> Maybe (Kind Void)) -- ^ Constructors
  -> (x -> Maybe (Kind Void)) -- ^ Variables
  -> (String, [x]) -- ^ Type constructor and arguments
  -> [[Ty x]] -- ^ Fields for each data constructor
  -> m (Either (KindError a) (Kind Void))
runInferDataDeclKind supply freezeVars a b c d =
  runExceptT $ inferDataDeclKind supply freezeVars a b c d

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

      res <- runInferKind supply pure ctorCtx varCtx (TyApp (TyCtor "A") (TyCtor "B"))
      res `shouldBe` Right KindRow

    it "2) A : Type, B : Row |- { l : A | B } : Row" $ do
      let
        ctorCtx =
          \case
            "A" -> Just KindType
            "B" -> Just KindRow
            _ -> Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

      res <- runInferKind supply pure ctorCtx varCtx (tyRowExtend (Label "l") (TyCtor "A") (TyCtor "B"))
      res `shouldBe` Right KindRow

    it "3) A : Type -> Row, B : Row |/- a b : Row" $ do
      let
        ctorCtx =
          \case
            "A" -> Just $ KindArr KindType KindRow
            "B" -> Just KindRow
            _ -> Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

      res <- runInferKind supply pure ctorCtx varCtx (TyApp (TyCtor "A") (TyCtor "B"))
      res `shouldBe` Left (KindMismatch KindType KindRow)

    it "4) Mu : ?0 -> Type, f : ?0, f (Mu f) : Type |- Mu : (Type -> Type) -> Type" $ do
      let
        ctorCtx = const Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

        ctorArgs = ("Mu", ["f"])
        branches = [[TyApp (TyVar "f") (TyApp (TyCtor "Mu") (TyVar "f"))]]

      res <- runInferDataDeclKind supply pure ctorCtx varCtx ctorArgs branches

      res `shouldBe` Right (KindArr (KindArr KindType KindType) KindType)

    it "5) Mu : ?0 -> Type, f : ?0, f f : Type |- occurs error" $ do
      let
        ctorCtx = const Nothing

        varCtx :: String -> Maybe (Kind Void)
        varCtx = const Nothing

        ctorArgs = ("Mu", ["f"])
        branches = [[TyApp (TyVar "f") (TyVar "f")]]

      res <- runInferDataDeclKind supply pure ctorCtx varCtx ctorArgs branches
      res `shouldBe` Left (KindOccurs 0 (KindArr (KindVar 0) (KindVar 1)))
