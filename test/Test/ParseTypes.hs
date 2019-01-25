{-# language OverloadedStrings #-}
{-# language LambdaCase #-}
{-# language TypeApplications #-}
module Test.ParseTypes where

import Control.Concurrent.Supply (Supply)
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec (parse, eof)

import qualified Data.Text as Text

import Desugar
import Kind
import Label
import Parser
import Ty

import Test.Types (runInferType)

import Test.Hspec

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
      Right tm -> do
        res <- liftIO $ runInferType a b c d (desugar tm)
        case res of
          Left err' -> error $ show err'
          Right{} -> pure () :: Expectation

parseTypesSpec :: Supply -> Spec
parseTypesSpec supply =
  describe "ParseTypes" $ do
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
