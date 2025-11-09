{-# LANGUAGE OverloadedStrings #-}

module ChoreoToNoname.TranslationSteps.SequentializeTranslationTest where

import qualified Types.LocalBehavior as LB
import Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqLocalBehavior (LCenter (..), LLeft (..), LRight (..), SeqLocalBehavior (..))
import Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SequentializeTranslation (sequentialize)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

tests :: TestTree
tests =
  testGroup
    "Sequentialize Tests"
    $ map
      mkTest
      [ testNil,
        testLockUnlock,
        testReceive
      ]

type TestCaseData = (String, LB.LocalBehavior, SeqLocalBehavior)

mkTest :: TestCaseData -> TestTree
mkTest (msg, localBehavior, expected) =
  testCase
    msg
    ( assertEqual
        msg
        (Right expected)
        (sequentialize localBehavior)
    )

-- BASICS --

testNil :: TestCaseData
testNil =
  let localBehavior = LB.LNil
      expected = L . C . LNew [] $ LNil
   in ("Nil", localBehavior, expected)

testLockUnlock :: TestCaseData
testLockUnlock =
  let localBehavior = LB.LLock . LB.LUnlock $ LB.LNil
      expected = L . C . LNew [] $ LNil
   in ("Lock-Unlock", localBehavior, expected)

testReceive :: TestCaseData
testReceive =
  let localBehavior = LB.LReceive "X0" LB.LNil
      expected = L . LReceive "X0" . C . LNew [] $ LNil
   in ("Receive", localBehavior, expected)
