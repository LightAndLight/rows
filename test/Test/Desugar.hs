{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
module Test.Desugar where

import Bound.Var (Var(..))
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec (parse, eof)

import qualified Data.Text as Text

import Desugar.Sections
import Parser
import Syntax (Syn(..))
import Ty

import qualified Syntax as Syn

import Test.Hspec

parseAndDesugar
  :: String -- ^ Test case
  -> (forall ty a. Syn ty a -> Syn ty a) -- ^ Desugaring
  -> String -- ^ Input term
  -> String -- ^ Expected term
  -> Spec
parseAndDesugar name f str str' =
  it (name <> ": " <> str) $
    case parse @Void (parseTm <* eof) "test" (Text.pack str) of
      Left err -> error $ show err
      Right tm ->
        case parse @Void (parseTm <* eof) "test" (Text.pack str') of
          Left err' -> error $ show err'
          Right tm' -> f tm `shouldBe` f tm'

desugarSpec :: Spec
desugarSpec =
  describe "Desugar" $ do
    describe "Sections" $ do
      it "merge test 1" $ do
        mergeWith @Text @Text
          SynApp
          ( 1
          , Syn.lam "a" $ SynApp (pure "x") (pure "a")
          )
          ( 2
          , Syn.lam "a" $
            Syn.lam "b" $
            SynApp (SynApp (pure "y") (pure "a")) (pure "b")
          )
          `shouldBe`
          ( 3
          , Syn.lam "a" $
            Syn.lam "b" $
            Syn.lam "c" $
            SynApp
              (SynApp (pure "x") (pure "a"))
              (SynApp (SynApp (pure "y") (pure "b")) (pure "c"))
          )
      it "shunt test 1" $ do
        shunt @Text @Text
          (\x -> SynAnn x $ TyCtor "T")
          ( 1
          , Syn.lam "a" $ SynApp (pure "x") (pure "a")
          )
          `shouldBe`
          ( 1
          , Syn.lam "a" $
            SynAnn (SynApp (pure "x") (pure "a")) (TyCtor "T")
          )
      it "wedge test 1 - makeSections( \\x -> x _ )" $ do
        wedge @Text @Text
          id
          (1, Syn.lam (F "a") $ SynApp (pure $ B ()) (pure $ F "a"))
          `shouldBe`
          ( 1
          , Syn.lam "a" $
            Syn.lam "b" $
            SynApp (pure "b") (pure "a")
          )
      it "wedge test 2 - makeSections( \\x -> x _ _ )" $ do
        wedge @Text @Text
          id
          ( 2
          , Syn.lam (F "a") $
            Syn.lam (F "b") $
            SynApp (SynApp (pure $ B ()) (pure $ F "a")) (pure $ F "b"))
          `shouldBe`
          ( 2
          , Syn.lam "a" $
            Syn.lam "b" $
            Syn.lam "c" $
            SynApp (SynApp (pure "c") (pure "a")) (pure "b")
          )
      it "wedge test 3 - makeSections( \\x -> _ _ x _ )" $ do
        wedge @Text @Text
          id
          ( 3
          , Syn.lam (F "a") $
            Syn.lam (F "b") $
            Syn.lam (F "c") $
            SynApp
              (SynApp
                  (SynApp (pure $ F "a") (pure $ F "b"))
                  (pure $ B ()))
              (pure $ F "c")
          )
          `shouldBe`
          ( 3
          , Syn.lam ("a") $
            Syn.lam ("b") $
            Syn.lam ("c") $
            Syn.lam ("d") $
            SynApp
              (SynApp
                  (SynApp (pure "a") (pure "b"))
                  (pure "d"))
              (pure "c")
          )
      parseAndDesugar
        "makeSections"
        makeSections
        "x _"
        "\\y -> x y"
      parseAndDesugar
        "makeSections"
        makeSections
        "\\x -> x _"
        "\\y -> \\x -> x y"
      parseAndDesugar
        "makeSections"
        makeSections
        "\\x -> \\y -> x y _"
        "\\z -> \\x -> \\y -> x y z"
      parseAndDesugar
        "makeSections"
        makeSections
        "\\x -> \\y -> x y _ _"
        "\\z -> \\w -> \\x -> \\y -> x y z w"
      parseAndDesugar
        "makeSections"
        makeSections
        "x (\\y -> y _ _)"
        "x (\\z -> \\w -> \\y -> y z w)"
      parseAndDesugar
        "makeSections"
        makeSections
        "x (_.l) (+{ m = _ })"
        "x (\\y -> y.l) (\\y -> +{ m = y })"
