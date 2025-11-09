{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Data.Traversable (mapAccumL)

import qualified Sapic.TermRewrite as EquationalTheoryExtension
import qualified Sapic.SapicTranslation as BaseTranslation
import qualified Sapic.TranslationWithEquationalOperators as DHTranslation


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Compiler.ToSapicPlus.Translation"
  [
    BaseTranslation.tests,
    EquationalTheoryExtension.tests,
    DHTranslation.tests
  ]