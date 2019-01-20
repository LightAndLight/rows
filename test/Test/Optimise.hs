{-# language LambdaCase #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
module Test.Optimise where

import Data.Generics.Plated1 (rewrite1)
import Data.Monoid (Sum(..))
import Data.Void (Void)
import Text.Megaparsec (parse, eof)

import qualified Data.Text as Text

import Desugar
import Eval
import Optimisation
import Parser
import Tm

import Test.Hspec

import Hedgehog
  ((===), MonadGen, Property, property, forAll, annotateShow, failure)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import HaskellWorks.Hspec.Hedgehog (require)

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

genAddition :: forall tyVar a m. MonadGen m => m a -> m (Tm tyVar a)
genAddition ma = go
  where
    go =
      Gen.recursive Gen.choice
        [ TmVar <$> ma, genTmInt ]
        [ TmAdd <$> go <*> go ]

    genTmInt = TmInt <$> Gen.int (Range.constant (-100) 100)

prop_foldAddition :: Property
prop_foldAddition =
  property $ do
    tm <- forAll $ genAddition @Void (pure ())
    let tm' = rewrite1 foldAddition tm
    annotateShow tm'

    let count = foldMapTmLeaves (\case; TmInt{} -> Sum 1; _ -> mempty) tm'
    case count :: Sum Int of
      0 -> pure ()
      1 -> pure ()
      _ -> failure

    let tm1 = (tm' >>= \_ -> TmInt 0) :: Tm Void ()
    annotateShow tm1

    let tm2 = (tm >>= \_ -> TmInt 0) :: Tm Void ()
    annotateShow tm2

    runSteps [stepAdd] tm1 === runSteps [stepAdd] tm2

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
    it "foldInts addition" $ require prop_foldAddition
