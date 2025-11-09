{-# LANGUAGE OverloadedStrings #-}

module Choreo.FrameTest (tests) where

import Types.Choreography (Term (..))
import Types.Rewrite (Frame)
import Choreography.Frame (applyFrame, initFrame)
import Types.Simple (FUNCTIONS (..))
import Types.LocalBehavior (Recipe (..))
import qualified Data.Map as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)
import Syntax.Util (stdConstructors)
import Choreography.Enricher (stdRewriteRules)

type TestCaseData = (String, Frame, Recipe, Term)

tests :: TestTree
tests =
  testGroup
    "Frame Tests"
    $ testInitFrame
      : map
        mkTest
        [ testApplyFrameDscrypt,
          testApplyFrameDcrypt,
          testApplyFrameOpen,
          testApplyFrameProj1,
          testApplyFrameProj2
        ]

mkTest :: TestCaseData -> TestTree
mkTest (msg, frame, recipe, expected) =
  testCase msg $
    let actual = applyFrame stdRewriteRules stdConstructors frame recipe
     in assertEqual
          ("Apply frame: " ++ msg)
          (Right expected)
          actual

-- FUNCTION : initFrame --

testInitFrame :: TestTree
testInitFrame =
  testCase "Init frame" $
    let result = initFrame [Atomic "k", Composed SCRYPT [Atomic "k", Atomic "msg", Atomic "r"]]
        expected = Map.fromList [("X0", Atomic "k"), ("X1", Composed SCRYPT [Atomic "k", Atomic "msg", Atomic "r"])]
     in assertEqual
          "Init frame"
          expected
          result

-- FUNCTION : applyFrame --

testApplyFrameDscrypt :: TestCaseData
testApplyFrameDscrypt =
  let frame = initFrame [Atomic "k", Composed SCRYPT [Atomic "k", Atomic "msg", Atomic "r"]]
      recipe = LComp DSCRYPT [LAtom "X0", LAtom "X1"]
      expected = Atomic "msg"
   in ("Dscrypt", frame, recipe, expected)

testApplyFrameDcrypt :: TestCaseData
testApplyFrameDcrypt =
  let frame = initFrame [Composed INV [Atomic "k"], Composed CRYPT [Atomic "k", Atomic "msg", Atomic "r"]]
      recipe = LComp DCRYPT [LAtom "X0", LAtom "X1"]
      expected = Atomic "msg"
   in ("Dcrypt", frame, recipe, expected)

testApplyFrameOpen :: TestCaseData
testApplyFrameOpen =
  let frame = initFrame [Atomic "k", Composed SIGN [Composed INV [Atomic "k"], Atomic "msg"]]
      recipe = LComp OPEN [LAtom "X0", LAtom "X1"]
      expected = Atomic "msg"
   in ("Open", frame, recipe, expected)

testApplyFrameProj1 :: TestCaseData
testApplyFrameProj1 =
  let frame = initFrame [Composed PAIR [Atomic "msg1", Atomic "msg2"]]
      recipe = LComp PROJ1 [LAtom "X0"]
      expected = Atomic "msg1"
   in ("Proj1", frame, recipe, expected)

testApplyFrameProj2 :: TestCaseData
testApplyFrameProj2 =
  let frame = initFrame [Composed PAIR [Atomic "msg1", Atomic "msg2"]]
      recipe = LComp PROJ2 [LAtom "X0"]
      expected = Atomic "msg2"
   in ("Proj2", frame, recipe, expected)
