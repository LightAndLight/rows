{-# language OverloadedStrings #-}
{-# language TypeApplications #-}
module Test.Parse where

import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec (parse, eof)

import qualified Data.Text as Text

import Desugar
import Label
import Parser
import Tm
import Ty

import Test.Hspec

testParseTmSuccess :: String -> Tm Text Text -> Spec
testParseTmSuccess str val =
  it str $
    desugar <$> parse @Void (parseTm <* eof) "test" (Text.pack str)
    `shouldBe`
    Right val

testParseTySuccess :: String -> Ty Text -> Spec
testParseTySuccess str val =
  it str $
    parse @Void (parseTy <* eof) "test" (Text.pack str) `shouldBe` Right val

parseSpec :: Spec
parseSpec =
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
