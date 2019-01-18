{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
module Main where

import Bound.Scope (toScope)
import Bound.Var (Var(..))
import Control.Concurrent.Supply (Supply, newSupply)
import Control.Monad.Except (runExcept)
import Control.Monad.State (evalStateT)
import Control.Monad.Trans.Class (lift)
import Data.Generics.Plated1 (rewrite1)
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec (parse, eof)

import qualified Data.Text as Text

import Inference.Kind
import Inference.Type
import Kind
import Label
import Meta
import Optimisation
import Parser
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
  :: (Ord b, Show b)
  => Supply
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (b -> Maybe (Kind Void)) -- ^ Type variables
  -> (c -> Either c (Ty b)) -- ^ Term variables
  -> Tm b c
  -> Either (TypeError Int b c) (Forall b)
runInferType supply a b c tm =
  runExcept $ inferType supply a b c tm

testParseTmSuccess :: String -> Tm Text Text -> Spec
testParseTmSuccess str val =
  it str $
    parse @Void (parseTm <* eof) "test" (Text.pack str) `shouldBe` Right val

testParseTySuccess :: String -> Ty Text -> Spec
testParseTySuccess str val =
  it str $
    parse @Void (parseTy <* eof) "test" (Text.pack str) `shouldBe` Right val

parseAndCheckTm
  :: Supply
  -> (String -> Maybe (Kind Void)) -- ^ Type constructors
  -> (Text -> Maybe (Kind Void)) -- ^ Type variables
  -> (Text -> Either Text (Ty Text)) -- ^ Term variables
  -> String -- ^ Term
  -> Spec
parseAndCheckTm a b c d str =
  it str $
    case parse @Void (parseTm <* eof) "test" (Text.pack str) of
      Left err -> error $ show err
      Right tm ->
        case runInferType a b c d tm of
          Left err' -> error $ show err'
          Right{} -> pure () :: Expectation

parseAndOptimise
  :: String -- ^ Optimisation name
  -> (forall ty a. Tm ty a -> Maybe (Tm ty a)) -- ^ Optmisation
  -> String -- ^ Input term
  -> String -- ^ Expected term
  -> Spec
parseAndOptimise name f str str' =
  it (name <> ": " <> str) $
    case parse @Void (parseTm <* eof) "test" (Text.pack str) of
      Left err -> error $ show err
      Right tm ->
        case parse @Void (parseTm <* eof) "test" (Text.pack str') of
          Left err' -> error $ show err'
          Right tm' -> rewrite1 f tm `shouldBe` tm'

main :: IO ()
main = do
  supply <- newSupply
  hspec $ do
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

      it "|- _.l : forall a r. Record (l : a | r) -> a" $ do
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
            (forAll ["a", "r"] $
             tyArr
               (tyRecord $ tyRowExtend (Label "l") (pure "a") (pure "r"))
               (pure "a"))

      it "|- (\\r -> r.f r.x) : forall a b r. Record (f : a -> b, x : a | r) -> b" $ do
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
             (TmApp (TmSelect $ Label "f") (pure "r"))
             (TmApp (TmSelect $ Label "x") (pure "r")))

          `shouldBe`

          Right
            (forAll ["a", "b", "r"] $
             tyArr
               (tyRecord $
                tyRowExtend (Label "f") (tyArr (pure "a") (pure "b")) $
                tyRowExtend (Label "x") (pure "a") $
                (pure "r"))
               (pure "b"))

      it "r : Record (x : A, y : B) |- r.y : B" $ do
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
          (TmApp (TmSelect $ Label "y") (pure "r"))

          `shouldBe`

          Right (forAll [] $ TyCtor "B")

      it "r : Row, x : Record (x : A | r) -> A, y : Record (y : A | r) |/- x y : A" $ do
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

      it "r : Row, x : Record (x : A, y : B | r) -> A, y : Record (y : A, X : B | r) |/- x y : A" $ do
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
    describe "Parse" $ do
      describe "Term" $ do
        testParseTmSuccess "x" (pure "x")
        testParseTmSuccess "\\x -> x" (lam "x" $ pure "x")
        testParseTmSuccess
          "\\x -> \\y -> x y"
          (lam "x" $ lam "y" $ TmApp (pure "x") (pure "y"))
        testParseTmSuccess
          "x - a - b"
          (tmRestrict (tmRestrict (pure "x") (Label "a")) (Label "b"))
        testParseTmSuccess
          "x.a.b"
          (tmSelect (tmSelect (pure "x") (Label "a")) (Label "b"))
        testParseTmSuccess
          "x.a.b - c"
          (tmSelect
            (tmSelect (pure "x") (Label "a"))
            (Label "b")
            `tmRestrict`
            Label "c")
        testParseTmSuccess
          "\\x -> x.a - b"
          (lam "x" $ tmSelect (pure "x") (Label "a") `tmRestrict` Label "b")
        testParseTmSuccess
          "(\\x -> x.a) - b"
          (lam "x" (tmSelect (pure "x") (Label "a")) `tmRestrict` Label "b")
        testParseTmSuccess
          "*{x = a | *{ y = b | *{ z = c | *{}}}}"
          (tmExtend (Label "x") (pure "a") $
          tmExtend (Label "y") (pure "b") $
          tmExtend (Label "z") (pure "c") $
          TmEmpty)
        testParseTmSuccess
          "*{x = a, y = b, z = c}"
          (tmExtend (Label "x") (pure "a") $
          tmExtend (Label "y") (pure "b") $
          tmExtend (Label "z") (pure "c") $
          TmEmpty)
        testParseTmSuccess
          "+{ a is x ? \\b -> b | \\c -> c }"
          (tmMatch (pure "a") (Label "x") (lam "b" $ pure "b") (lam "c" $ pure "c"))
        testParseTmSuccess
          "+{ a is x ? b | \\a' -> +{ a' is y ? d | \\a'' -> a'' }}"
          (tmMatch (pure "a") (Label "x") (pure "b") $ lam "a'" $
           tmMatch (pure "a'") (Label "y") (pure "d") $ lam "a''" $
           pure "a''")
        testParseTmSuccess
          "+{ a = b }"
          (tmInject (Label "a") (pure "b"))
        testParseTmSuccess
          "+{ a | +{ b | c }}"
          (tmEmbed (Label "a") $
          tmEmbed (Label "b") $
          pure "c")
        testParseTmSuccess
          "+{ a, b | c }"
          (tmEmbed (Label "a") $
           tmEmbed (Label "b") $
           pure "c")
        testParseTmSuccess "a : T" (TmAnn (pure "a") (TyCtor "T"))
        testParseTmSuccess
          "a b : T"
          (TmAnn (TmApp (pure "a") (pure "b")) (TyCtor "T"))
        testParseTmSuccess
          "a (b : T)"
          (TmApp (pure "a") (TmAnn (pure "b") (TyCtor "T")))
        testParseTmSuccess
          "\\x -> y : T"
          (lam "x" $ TmAnn (pure "y") (TyCtor "T"))
        testParseTmSuccess
          "(\\x -> y) : T"
          (TmAnn (lam "x" $ pure "y") (TyCtor "T"))
        testParseTmSuccess
          "*{ x = a }.x"
          (tmSelect (tmExtend (Label "x") (pure "a") TmEmpty) (Label "x"))
      describe "Type" $ do
        testParseTySuccess "(->)" TyArr
        testParseTySuccess "(->) a b" (tyArr (pure "a") (pure "b"))
        testParseTySuccess "a -> b" (tyArr (pure "a") (pure "b"))
        testParseTySuccess
          "f a -> b"
          (tyArr (TyApp (pure "f") (pure "a")) (pure "b"))
        testParseTySuccess
          "a -> b -> Record ()"
          (tyArr (pure "a") (tyArr (pure "b") (tyRecord TyRowEmpty)))
        testParseTySuccess
          "a -> b -> Variant () a"
          (tyArr (pure "a") $
           tyArr (pure "b") $
           TyApp (tyVariant TyRowEmpty) (pure "a"))
        testParseTySuccess
          "a -> b -> Variant (() a)"
          (tyArr (pure "a") $
           tyArr (pure "b") $
           tyVariant (TyApp TyRowEmpty (pure "a")))
        testParseTySuccess
          "(a : A | (b : B | ()))"
          (tyRowExtend (Label "a") (TyCtor "A") $
           tyRowExtend (Label "b") (TyCtor "B") $
           TyRowEmpty)
        testParseTySuccess
          "(a : A, b : B)"
          (tyRowExtend (Label "a") (TyCtor "A") $
           tyRowExtend (Label "b") (TyCtor "B") $
           TyRowEmpty)
        testParseTySuccess
          "(a : A | (b : B | (c : C | r)))"
          (tyRowExtend (Label "a") (TyCtor "A") $
           tyRowExtend (Label "b") (TyCtor "B") $
           tyRowExtend (Label "c") (TyCtor "C") $
           pure "r")
        testParseTySuccess
          "(a : A, b : B, c : C | r)"
          (tyRowExtend (Label "a") (TyCtor "A") $
           tyRowExtend (Label "b") (TyCtor "B") $
           tyRowExtend (Label "c") (TyCtor "C") $
           pure "r")
    describe "Check" $ do
      parseAndCheckTm
        supply
        (\case
            "A" -> Just KindType
            _ -> Nothing)
        (const Nothing)
        Left
        "(\\x -> x) : A -> A"
      parseAndCheckTm
        supply
        (\case
            "A" -> Just KindType
            "B" -> Just KindType
            _ -> Nothing)
        (\case
            "r" -> Just KindRow
            _ -> Nothing)
        (\case
            "b" ->
              Right $
              tyArr (TyCtor "A") $
              tyVariant $
              tyRowExtend (Label "y") (TyCtor "B") $
              (pure "r")
            a -> Left a)
        "(\\l -> +{ l is x ? b | \\y -> y}) : Variant (x : A, y : B | r) -> Variant (y : B | r)"
      parseAndCheckTm
        supply
        (\case
            "A" -> Just KindType
            "B" -> Just KindType
            _ -> Nothing)
        (\case
            "r" -> Just KindRow
            _ -> Nothing)
        (\case
            "b" ->
              Right $
              tyArr (TyCtor "A") $
              tyVariant $
              tyRowExtend (Label "y") (TyCtor "B") $
              (pure "r")
            a -> Left a)
        "(\\l -> +{ l is x ? b | \\y -> y}) : Variant (y : B, x : A | r) -> Variant (y : B | r)"
    describe "Optimise" $ do
      parseAndOptimise "etaReduce" etaReduce "\\x -> f x" "f"
      parseAndOptimise "etaReduce" etaReduce "\\x -> f x x" "\\x -> f x x"
      parseAndOptimise "recordElim" recordElim "*{ x = a }.x" "a"
      parseAndOptimise "recordElim" recordElim "*{ y = a, x = b }.x" "b"
      parseAndOptimise "variantElim" variantElim "+{ +{ x = a } is x ? f | g }" "f a"
      parseAndOptimise "variantElim" variantElim "+{ +{ x = a } is y ? f | \\b -> +{ b is x ? g | h } }" "g a"
      parseAndOptimise "variantElim" variantElim "+{ +{ x = a } is y ? f | g }" "g +{ x = a }"
