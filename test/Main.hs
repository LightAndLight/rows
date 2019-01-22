{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
module Main where

import Control.Concurrent.Supply (newSupply)

import Test.Hspec

import Test.Desugar
import Test.Kinds
import Test.Optimise
import Test.Parse
import Test.ParseTypes
import Test.Types

main :: IO ()
main = do
  supply <- newSupply
  hspec $ do
    desugarSpec
    kindsSpec supply
    optimiseSpec
    parseSpec
    parseTypesSpec supply
    typesSpec supply
