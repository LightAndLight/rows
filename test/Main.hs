{-# language LambdaCase #-}
module Main where

import Bound.Scope (toScope)
import Bound.Var (Var(..))
import Control.Concurrent.Supply (Supply, newSupply)
import Control.Monad.Except (runExcept)
import Control.Monad.State (evalStateT)
import Control.Monad.Trans.Class (lift)
import Data.Void (Void)

import Inference.Kind
import Inference.Type
import Kind
import Meta
import Tm
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

runInferType
  :: Ord b
  => Supply
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (b -> Maybe (Kind Void)) -- ^ Type variables
  -> (c -> Either c (Ty b)) -- ^ Type variables
  -> Tm c
  -> Either (TypeError Int b c) (Forall b)
runInferType supply a b c tm =
  runExcept $ evalStateT (inferType a b c tm) supply

main :: IO ()
main = do
  supply <- newSupply
  hspec $ do
    describe "Kinds" $ do
      it "A : Type -> Row, B : Type |- a b : Row" $ do
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

      it "A : Type -> Row, B : Row |/- a b : Row" $ do
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

      it "Mu : ?0 -> Type, f : ?0, f (Mu f) : Type |- Mu : (Type -> Type) -> Type" $ do
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

      it "Mu : ?0 -> Type, f : ?0, f f : Type |- occurs error" $ do
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
    describe "Types" $ do
      it "|- (\\x -> x) : forall a. a -> a" $ do
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

          Right (Forall 1 $ toScope $ TyApp (TyApp TyArr (TyVar (B 0))) (TyVar (B 0)))

      it "|- (\\x y -> x) : forall a b. a -> b -> a" $ do
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
            (Forall 2 $ toScope $
             TyApp (TyApp TyArr (TyVar (B 0)))
             (TyApp (TyApp TyArr (TyVar (B 1))) (TyVar (B 0))))

      it "(\\x -> x x) occurs error" $ do
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

      it "f : X -> Y, x : Z |/- f x : Y" $ do
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
