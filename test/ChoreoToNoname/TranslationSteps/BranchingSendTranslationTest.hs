{-# LANGUAGE OverloadedStrings #-}

module ChoreoToNoname.TranslationSteps.BranchingSendTranslationTest where

import Types.Simple (Mode(..))
import Types.LocalBehavior (Formula (Equality), Label, LocalAtomic (..), LocalBehavior (..), Recipe (..))
import Compiler.ToNoname.ChoreoToNoname.TranslationSteps.BranchingSendTranslation (removeBranchingSend)
import qualified Data.Text as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

tests :: TestTree
tests =
  testGroup
    "Branching Send Translation Tests"
    $ map
      mkTest
      [ testNil,
        testReceive,
        testOneChoice,
        testTwoChoices,
        testThreeChoices,
        testMultipleChoices,
        testWrapSendLockUnlock,
        testWrapSendReceive,
        testWrapSendAtomic,
        testSeqSend
      ]

type TestCaseData = (String, LocalBehavior, LocalBehavior)

mkTest :: TestCaseData -> TestTree
mkTest (msg, localBehavior, expected) =
  testCase
    msg
    ( assertEqual
        msg
        expected
        (removeBranchingSend localBehavior)
    )

ifs :: Label -> T.Text -> (LocalAtomic -> LocalAtomic)
ifs num msg =
  LIf
    (LAtom "B0")
    (LAtom num)
    (LUnlock $ LSend [(LAtom msg, LNil)])

twoChoices :: [(Recipe, LocalBehavior)]
twoChoices = [(LAtom "msg1", LNil), (LAtom "msg2", LNil)]

-- NO BRANCHING SENDS --

testNil :: TestCaseData
testNil =
  let localBehavior = LNil
   in ("Nil", localBehavior, localBehavior)

testReceive :: TestCaseData
testReceive =
  let localBehavior = LReceive "X0" LNil
   in ("Receive", localBehavior, localBehavior)

-- SIMPLE BRANCHING SENDS --

testOneChoice :: TestCaseData
testOneChoice =
  let localBehavior = LSend [(LAtom "X0", LNil)]
   in ("Single send", localBehavior, localBehavior)

testTwoChoices :: TestCaseData
testTwoChoices =
  let localBehavior = LSend twoChoices
      choice = LChoice Diamond "B0" ["N0", "N1"]
      iff =
        LIf
          (LAtom "B0")
          (LAtom "N0")
          (LUnlock $ LSend [(LAtom "msg1", LNil)])
          (LUnlock $ LSend [(LAtom "msg2", LNil)])
      expected = LLock . choice $ iff
   in ("Two choices", localBehavior, expected)

testThreeChoices :: TestCaseData
testThreeChoices =
  let localBehavior = LSend $ twoChoices ++ [(LAtom "msg3", LNil)]
      choice = LChoice Diamond "B0" ["N0", "N1", "N2"]
      if1 =
        LIf
          (LAtom "B0")
          (LAtom "N0")
          (LUnlock $ LSend [(LAtom "msg1", LNil)])
      if2 =
        LIf
          (LAtom "B0")
          (LAtom "N1")
          (LUnlock $ LSend [(LAtom "msg2", LNil)])
          (LUnlock $ LSend [(LAtom "msg3", LNil)])
      expected = LLock . choice . if1 $ if2
   in ("MultipleChoices", localBehavior, expected)

testMultipleChoices :: TestCaseData
testMultipleChoices =
  let localBehavior =
        LSend
          [ (LAtom "msg1", LNil),
            (LAtom "msg2", LNil),
            (LAtom "msg3", LNil),
            (LAtom "msg4", LNil),
            (LAtom "msg5", LNil)
          ]
      choice = LChoice Diamond "B0" ["N0", "N1", "N2", "N3", "N4"]
      expected =
        LLock
          . choice
          . ifs "N0" "msg1"
          . ifs "N1" "msg2"
          . ifs "N2" "msg3"
          . ifs "N3" "msg4"
          $ LUnlock
          $ LSend [(LAtom "msg5", LNil)]
   in ("MultipleChoices", localBehavior, expected)

-- WRAPPED SENDS --

testWrapSendLockUnlock :: TestCaseData
testWrapSendLockUnlock =
  let localBehavior = LLock . LUnlock $ LSend twoChoices
      choice = LChoice Diamond "B0" ["N0", "N1"]
      expected =
        LLock
          . LUnlock
          . LLock
          . choice
          . ifs "N0" "msg1"
          $ LUnlock
          $ LSend [(LAtom "msg2", LNil)]
   in ("Wrapped send, lock-unlock", localBehavior, expected)

testWrapSendReceive :: TestCaseData
testWrapSendReceive =
  let localBehavior = LReceive "X0" $ LSend twoChoices
      choice = LChoice Diamond "B0" ["N0", "N1"]
      expected =
        LReceive "X0"
          . LLock
          . choice
          . ifs "N0" "msg1"
          $ LUnlock
          $ LSend [(LAtom "msg2", LNil)]
   in ("Wrapped send, receive", localBehavior, expected)

testWrapSendAtomic :: TestCaseData
testWrapSendAtomic =
  let localBehavior =
        LLock
          . LNew "X0"
          . LRead "X1" "cell" (LAtom "X0")
          . LWrite "cell" (LAtom "X1") (LAtom "X0")
          . (\x -> LIf (LAtom "X0") (LAtom "X1") x (LUnlock LNil))
          . LChoice Star "X2" ["test"]
          . LRelease Star (Equality (LAtom "X0") (LAtom "X1"))
          . LUnlock
      choice = LChoice Diamond "B0" ["N0", "N1"]
      expected =
        localBehavior
          . LLock
          . choice
          . ifs "N0" "msg1"
          $ LUnlock
          $ LSend [(LAtom "msg2", LNil)]
   in ("Wrapped send, atomic", localBehavior $ LSend twoChoices, expected)

-- SEQUENCIALIZED SEND --

testSeqSend :: TestCaseData
testSeqSend =
  let localBehavior =
        LSend
          [ ( LAtom "X0",
              LSend
                [ (LAtom "X2", LNil),
                  (LAtom "X3", LNil)
                ]
            ),
            ( LAtom "X1",
              LSend
                [ (LAtom "X2", LNil),
                  (LAtom "X3", LNil)
                ]
            )
          ]
      branch =
        LLock
          . LChoice Diamond "B1" ["N0", "N1"]
          $ LIf
            (LAtom "B1")
            (LAtom "N0")
            (LUnlock $ LSend [(LAtom "X2", LNil)])
            (LUnlock $ LSend [(LAtom "X3", LNil)])
      expected =
        LLock
          . LChoice Diamond "B0" ["N0", "N1"]
          $ LIf
            (LAtom "B0")
            (LAtom "N0")
            (LUnlock $ LSend [(LAtom "X0", branch)])
            (LUnlock $ LSend [(LAtom "X1", branch)])
   in ("Seq send", localBehavior, expected)
