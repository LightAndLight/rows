{-# language RankNTypes #-}
{-# language TypeApplications #-}
module Test.Optimise where

import Data.Generics.Plated1 (rewrite1)
import Data.Void (Void)
import Text.Megaparsec (parse, eof)

import qualified Data.Text as Text

import Desugar
import Optimisation
import Parser
import Tm

import Test.Hspec

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
          Right tm' -> rewrite1 f (desugar tm) `shouldBe` desugar tm'

optimiseSpec :: Spec
optimiseSpec =
  describe "Optimise" $ do
    parseAndOptimise "etaReduce" etaReduce "\\x -> f x" "f"
    parseAndOptimise "etaReduce" etaReduce "\\x -> f x x" "\\x -> f x x"
    parseAndOptimise "recordElim" recordElim "*{ x = a }.x" "a"
    parseAndOptimise "recordElim" recordElim "*{ y = a, x = b }.x" "b"
    parseAndOptimise "variantElim" variantElim "+{ +{ x = a } is x ? f | g }" "f a"
    parseAndOptimise "variantElim" variantElim "+{ +{ x = a } is y ? f | \\b -> +{ b is x ? g | h } }" "g a"
    parseAndOptimise "variantElim" variantElim "+{ +{ x = a } is y ? f | g }" "g +{ x = a }"
