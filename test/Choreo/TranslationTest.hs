{-# LANGUAGE OverloadedStrings #-}

module Choreo.TranslationTest (tests) where

import Types.Choreography (Agent, Atomic (..), CDefault (..), Choreography (..), Term (..))
import qualified Types.Choreography as Choreo
import Choreography.Frame (initFrame)
import Types.Simple (FUNCTIONS (..))
import Syntax.Util (stdConstructors)
import Types.LocalBehavior (LocalAtomic (..), LocalBehavior (..), Recipe (..))
import qualified Types.LocalBehavior as Local
import qualified Types.Simple as S
import Types.Rewrite (RewriteRule, TranslationError (..), TranslationResult, Description(..))
import qualified Types.Rewrite as RR
import Choreography.State (mkState)
import Compiler.ToLocalBehavior.Translation (translate, translateWith, translateWithDescription)

import Choreography.Enricher (stdRewriteRules)

import Compiler.ToLocalBehavior.TranslationCases.StateHint (translateStateHint)
import Compiler.ToLocalBehavior.TranslationCases.Lock (translateLock)
import Compiler.ToLocalBehavior.TranslationCases.Send (translateSend)
import Compiler.ToLocalBehavior.TranslationCases.Receive (extractReceive, constructReceiveIfs)

import qualified Data.Bifunctor as Bifunctor
import qualified Data.Map as Map
import qualified Data.Text as T
import Examples (protocolBAC)
import Types.ChoreographyProtocolShell (RoleKnowledge (RoleKnowledge))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

tests :: TestTree
tests =
  testGroup
    "Translation Tests"
    [ testGroup
        "Atomic This"
        $ map
          mkTestAtomicThis
          [ testLockUnlockThis,
            testNonceThis,
            testReadThis,
            testChoiceThis,
            testReleaseThis
          ],
      testGroup "Atomic Other" $
        map
          mkTestAtomicOther
          [ testLockUnlockOther,
            testNonceOther,
            testReadOther,
            testChoiceOther,
            testReleaseOther
          ],
      testGroup
        "Send"
        $ map
          mkTestSend
          [ testConstructSend1,
            testConstructSend2,
            testConstructSend3,
            testConstructSendFailRecipe,
            testConstructSendFailChoiceNo,
            testConstructSendFailSameAgent
          ],
      testGroup
        "Receiver"
        [ testExtractReceive,
          testTranslateReceiveHelper
        ],
      testGroup
        "Communication"
        $ map
          mkTestCommunication
          [ testCommunicationOneMsgA,
            testCommunicationOneMsgANoKnowledge,
            testCommunicationOneMsgB,
            testCommunicationOneMsgB2,
            testCommunicationOneMsgC,
            testCommunicationTwoMsgA,
            testCommunicationTwoMsgB,
            testCommunicationTwoMsgC,
            testCommunicationTwoConsecutiveMsgA,
            testCommunicationTwoConsecutiveMsgB,
            testCommunicationTwoConsecutiveMsgC,
            testCommunicationTwoBranchesB,
            testCommunicationTwoBranchesBNoKnowledge,
            testCommunicationThreeMsgA,
            testCommunicationThreeMsgB,
            testCommunicationThreeMsgBNoKnowledge,
            testCommunicationMultipleChecksA,
            testCommunicationDefault,
            testCommunicationCryptoA,
            testCommunicationAfterLockA,
            testCommunicationAfterLockB,
            testCommunicationSendReceived,
            testCommunicationSendReceivedScrypt,
            testCommunicationSendReceivedScrypt2,
            testCommunicationSendReceivedCrypt,
            testCommunicationSendReceivedPair,
            testCommunicationSendReceivedPairPair
          ],
      testGroup
        "Rewrite"
        [mkTestRewrite testRewriteSendReceivedSession]
        -- EXAMPLES --
        -- testExampleBACprotocolC
    ]

-- ATOMIC -- EXAMPLES --

exampleLockUnlock :: Choreography
exampleLockUnlock = Lock "A" $ Unlock Nil

exampleNonce :: Choreography
exampleNonce = Lock "A" . Nonce "x" $ Unlock Nil

exampleRead :: Choreography
exampleRead = Lock "A" . Nonce "x" . Read "y" "Cell" (Atomic "x") $ Unlock Nil

exampleChoice :: Choreography
exampleChoice = Lock "A" . Choice S.Star "x" ["t1", "t1"] $ Unlock Nil

exampleRelease :: Choreography
exampleRelease = Lock "A" . Release S.Star Choreo.Top $ Unlock Nil

--  ATOMIC -- HELPERS --

type TestCaseDataAtomicThis = (String, Choreography, LocalBehavior)

type TestCaseDataAtomicOther = (String, Choreography)

mkTestAtomicThis :: TestCaseDataAtomicThis -> TestTree
mkTestAtomicThis (msg, choreo, expected) =
  testCase
    msg
    ( assertEqual
        (msg ++ " , this agent")
        (translate "A" [(mkState $ RoleKnowledge [] [], choreo)])
        (Right expected)
    )

mkTestAtomicOther :: TestCaseDataAtomicOther -> TestTree
mkTestAtomicOther (msg, choreo) =
  testCase
    msg
    ( assertEqual
        (msg ++ " , other agent")
        (translate "B" [(mkState $ RoleKnowledge [] [], choreo)])
        (Right LNil)
    )

-- ATOMIC -- TESTS --

testLockUnlockThis :: TestCaseDataAtomicThis
testLockUnlockThis = ("Lock unlock", exampleLockUnlock, LLock $ LUnlock LNil)

testLockUnlockOther :: TestCaseDataAtomicOther
testLockUnlockOther = ("Lock unlock", exampleLockUnlock)

testNonceThis :: TestCaseDataAtomicThis
testNonceThis = ("Nonce", exampleNonce, LLock . LNew "X0" $ LUnlock LNil)

testNonceOther :: TestCaseDataAtomicOther
testNonceOther = ("Nonce", exampleNonce)

testReadThis :: TestCaseDataAtomicThis
testReadThis = ("Read", exampleRead, LLock . LNew "X0" . LRead "X1" "Cell" (LAtom "X0") $ LUnlock LNil)

testReadOther :: TestCaseDataAtomicOther
testReadOther = ("Read", exampleRead)

testChoiceThis :: TestCaseDataAtomicThis
testChoiceThis = ("Choice", exampleChoice, LLock . LChoice S.Star "X0" ["t1", "t1"] $ LUnlock LNil)

testChoiceOther :: TestCaseDataAtomicOther
testChoiceOther = ("Choice", exampleChoice)

testReleaseThis :: TestCaseDataAtomicThis
testReleaseThis = ("Release", exampleRelease, LLock . LRelease S.Star Local.Top $ LUnlock LNil)

testReleaseOther :: TestCaseDataAtomicOther
testReleaseOther = ("Release", exampleRelease)

-- SENDER --

type TestCaseDataSend = (String, Int, TranslationResult LocalBehavior, [([Term], Choreography)])

mkTestSend :: TestCaseDataSend -> TestTree
mkTestSend (msg, i, expected, fcs) =
  testCase
    msg
    ( assertEqual
        ("construct send " ++ msg)
        expected
        (translateSend translateWithDescription i (mkDescription "A") (map (Bifunctor.first (mkState . flip RoleKnowledge [])) fcs))
    )

testConstructSend1 :: TestCaseDataSend
testConstructSend1 =
  let msg1 = Atomic "msg1"
      terms = [msg1]
      choreo = Interaction "A" "B" [(msg1, Nil)] Epsilon
      expected = LSend [(LAtom "X0", LNil)]
   in ("One msg", 1, Right expected, [(terms, choreo)])

testConstructSend2 :: TestCaseDataSend
testConstructSend2 =
  let msg1 = Atomic "msg1"
      msg2 = Atomic "msg2"
      terms = [msg1, msg2]
      choreo = Interaction "A" "B" [(msg1, Nil), (msg2, Nil)] Epsilon
      expected = LSend [(LAtom "X0", LNil), (LAtom "X1", LNil)]
   in ("Two msgs", 2, Right expected, [(terms, choreo)])

testConstructSend3 :: TestCaseDataSend
testConstructSend3 =
  let msg1 = Atomic "msg1"
      msg2 = Atomic "msg2"
      msg3 = Atomic "msg3"
      terms = [msg1, msg2, msg3]
      choreo = Interaction "A" "B" [(msg1, Nil), (msg2, Nil), (msg3, Nil)] Epsilon
      expected = LSend [(LAtom "X0", LNil), (LAtom "X1", LNil), (LAtom "X2", LNil)]
   in ("Three msgs", 3, Right expected, [(terms, choreo)])

testConstructSendFailRecipe :: TestCaseDataSend
testConstructSendFailRecipe =
  let msg1 = Atomic "msg1"
      terms = []
      choreo = Interaction "A" "B" [(msg1, Nil)] Epsilon
   in ("fail recipe", 1, Left . NoRecipe $ [(initFrame terms, Atomic "msg1")], [(terms, choreo)])

testConstructSendFailChoiceNo :: TestCaseDataSend
testConstructSendFailChoiceNo =
  let msg1 = Atomic "msg1"
      msg2 = Atomic "msg2"
      msg3 = Atomic "msg3"
      terms = [msg1, msg2, msg3]
      choreo1 = Interaction "A" "B" [(msg1, Nil)] Epsilon
      choreo2 = Interaction "A" "B" [(msg2, Nil), (msg3, Nil)] Epsilon
   in ( "fail choice no",
        1,
        Left DifferentBranchLength,
        [(terms, choreo1), (terms, choreo2)]
      )

testConstructSendFailSameAgent :: TestCaseDataSend
testConstructSendFailSameAgent =
  let msg1 = Atomic "msg1"
      terms = []
      choreo1 = Interaction "A" "B" [(msg1, Nil)] Epsilon
      choreo2 = Interaction "B" "A" [(msg1, Nil)] Epsilon
      expected = Left $ DifferentAgents "A" "B"
   in ( "fail same agent",
        1,
        expected,
        [(terms, choreo1), (terms, choreo2)]
      )

-- RECEIVER --

testExtractReceive :: TestTree
testExtractReceive =
  let terms = [Atomic "msg1", Atomic "msg2", Atomic "msg3"]
      choreo = Interaction "A" "B" [(Atomic "msg1", Nil), (Atomic "msg2", Nil), (Atomic "msg3", Nil)] Epsilon
      terms1 = terms ++ [Atomic "msg1"]
      terms2 = terms ++ [Atomic "msg2"]
      terms3 = terms ++ [Atomic "msg3"]
      expected =
        ( [ (mkState $ RoleKnowledge terms1 [], Nil),
            (mkState $ RoleKnowledge terms2 [], Nil),
            (mkState $ RoleKnowledge terms3 [], Nil)
          ],
          [(mkState $ RoleKnowledge terms [], Epsilon)]
        )
   in testCase
        "Extract Receive"
        ( assertEqual
            "Extract receive"
            (Right expected)
            (extractReceive "X3" "B" [(mkState $ RoleKnowledge terms [], choreo)])
        )

testTranslateReceiveHelper :: TestTree
testTranslateReceiveHelper =
  let terms = [Atomic "msg1", Atomic "msg2", Atomic "msg3"]
      terms1 = terms ++ [Atomic "msg1"]
      terms2 = terms ++ [Atomic "msg2"]
      terms3 = terms ++ [Atomic "msg3"]
      choreo = Lock "A" $ Unlock Nil
      checks = [(LAtom "X0", LAtom "X3"), (LAtom "X1", LAtom "X3"), (LAtom "X2", LAtom "X3")]
      fcs = map (Bifunctor.first (mkState . flip RoleKnowledge [])) [(terms1, choreo), (terms2, choreo), (terms3, choreo)]
      ifx0x3 = LIf (LAtom "X0") (LAtom "X3")
      ifx1x3 = LIf (LAtom "X1") (LAtom "X3")
      ifx2x3 = LIf (LAtom "X2") (LAtom "X3")
      nil = LUnlock LNil
      local = LUnlock . LLock $ LUnlock LNil
      expected = ifx0x3 (ifx1x3 nil (ifx2x3 nil local)) (ifx1x3 (ifx2x3 nil local) (ifx2x3 local nil))
   in testCase
        "Receive Translation"
        ( assertEqual
            "Receive translation"
            (Right expected)
            (constructReceiveIfs translateWithDescription LNil (mkDescription "A") checks fcs)
        )

-- COMMUNICATION -- HELPERS --

type TestCaseDataCommunication = (T.Text, String, [Term], Choreography, TranslationResult LocalBehavior)

mkTestCommunication :: TestCaseDataCommunication -> TestTree
mkTestCommunication (agent, msg, frame, choreo, expected) =
  testCase
    (msg ++ ", " ++ T.unpack agent)
    ( assertEqual
        ("Communication, " ++ msg)
        expected
        (translate agent [(mkState $ RoleKnowledge frame [], choreo)])
    )

-- COMMUNICATION -- TESTS --

-- COMMUNICATION -- Example: one message --

exampleCommunicationOneMsg :: Choreography
exampleCommunicationOneMsg =
  Interaction "A" "B" [(Atomic "msg", Nil)] Epsilon

testCommunicationOneMsgA :: TestCaseDataCommunication
testCommunicationOneMsgA =
  ( "A",
    "one message",
    [Atomic "msg"],
    exampleCommunicationOneMsg,
    Right $ LSend [(LAtom "X0", LNil)]
  )

testCommunicationOneMsgANoKnowledge :: TestCaseDataCommunication
testCommunicationOneMsgANoKnowledge =
  ( "A",
    "one message, no knowledge",
    [],
    exampleCommunicationOneMsg,
    Left . NoRecipe $ [(Map.empty, Atomic "msg")]
  )

testCommunicationOneMsgB :: TestCaseDataCommunication
testCommunicationOneMsgB = ("B", "one message", [], exampleCommunicationOneMsg, Right $ LReceive "X0" LNil)

testCommunicationOneMsgB2 :: TestCaseDataCommunication
testCommunicationOneMsgB2 =
  ( "B",
    "one message, in frame",
    [Atomic "msg"],
    exampleCommunicationOneMsg,
    Right . LReceive "X1" . LLock $ LIf (LAtom "X0") (LAtom "X1") (LUnlock LNil) (LUnlock LNil)
  )

testCommunicationOneMsgC :: TestCaseDataCommunication
testCommunicationOneMsgC =
  ( "C",
    "one message",
    [],
    exampleCommunicationOneMsg,
    Right LNil
  )

-- COMMUNICATION -- Example: choice of two messages --

exampleCommunicationTwoMsg :: Choreography
exampleCommunicationTwoMsg =
  Interaction "A" "B" [(Atomic "msg1", Nil), (Atomic "msg2", Nil)] Epsilon

testCommunicationTwoMsgA :: TestCaseDataCommunication
testCommunicationTwoMsgA =
  ( "A",
    "two messages",
    [Atomic "msg1", Atomic "msg2"],
    exampleCommunicationTwoMsg,
    Right $ LSend [(LAtom "X0", LNil), (LAtom "X1", LNil)]
  )

testCommunicationTwoMsgB :: TestCaseDataCommunication
testCommunicationTwoMsgB =
  ( "B",
    "two messages",
    [],
    exampleCommunicationTwoMsg,
    Right $ LReceive "X0" LNil
  )

testCommunicationTwoMsgB2 :: TestCaseDataCommunication
testCommunicationTwoMsgB2 =
  ( "B",
    "two messages",
    [Atomic "msg1", Atomic "msg2"],
    exampleCommunicationTwoMsg,
    Right $
      LReceive "X2" (LLock $ LIf (LAtom "X0") (LAtom "X2") (LUnlock LNil) (LIf (LAtom "X1") (LAtom "X2") (LUnlock LNil) (LUnlock LNil)))
  )

testCommunicationTwoMsgC :: TestCaseDataCommunication
testCommunicationTwoMsgC =
  ( "C",
    "two messages",
    [],
    exampleCommunicationTwoMsg,
    Right LNil
  )

-- COMMUNICATION -- Example: consecutive messages --

exampleCommunicationTwoConsecutiveMsg :: Choreography
exampleCommunicationTwoConsecutiveMsg =
  Interaction "A" "B" [(Atomic "NA", Interaction "B" "A" [(Atomic "NB", Nil)] Epsilon)] Epsilon

testCommunicationTwoConsecutiveMsgA :: TestCaseDataCommunication
testCommunicationTwoConsecutiveMsgA =
  ( "A",
    "two consecutive messages",
    [Atomic "NA"],
    exampleCommunicationTwoConsecutiveMsg,
    Right $ LSend [(LAtom "X0", LReceive "X1" LNil)]
  )

testCommunicationTwoConsecutiveMsgB :: TestCaseDataCommunication
testCommunicationTwoConsecutiveMsgB =
  ( "B",
    "two consecutive messages",
    [Atomic "NB"],
    exampleCommunicationTwoConsecutiveMsg,
    Right . LReceive "X1" $ LSend [(LAtom "X0", LNil)]
  )

testCommunicationTwoConsecutiveMsgC :: TestCaseDataCommunication
testCommunicationTwoConsecutiveMsgC =
  ( "C",
    "two consecutive messages",
    [],
    exampleCommunicationTwoConsecutiveMsg,
    Right LNil
  )

-- COMMUNICATION -- Example: two branches --
exampleCommunicationTwoBranches :: Choreography
exampleCommunicationTwoBranches =
  Interaction "A" "B" [(Atomic "msg1", Lock "B" $ Unlock Nil), (Atomic "msg2", Nil)] Epsilon

testCommunicationTwoBranchesB :: TestCaseDataCommunication
testCommunicationTwoBranchesB =
  ( "B",
    "Two branches",
    [Atomic "msg1"],
    exampleCommunicationTwoBranches,
    Right
      . LReceive
        "X1"
      . LLock
      $ LIf (LAtom "X0") (LAtom "X1") (LUnlock . LLock $ LUnlock LNil) (LUnlock LNil)
  )

testCommunicationTwoBranchesBNoKnowledge :: TestCaseDataCommunication
testCommunicationTwoBranchesBNoKnowledge =
  ( "B",
    "Two branches, no knowledge",
    [],
    exampleCommunicationTwoBranches,
    Left $ DifferentTypes "lock"
  )

-- COMMUNICATION -- Example: choice of three messages --

exampleCommunicationThreeMsg :: Choreography
exampleCommunicationThreeMsg =
  let lockB = Lock "B" $ Unlock Nil
   in Interaction "A" "B" [(Atomic "msg1", lockB), (Atomic "msg2", lockB), (Atomic "msg3", lockB)] Epsilon

testCommunicationThreeMsgA :: TestCaseDataCommunication
testCommunicationThreeMsgA =
  ( "A",
    "three messages",
    [Atomic "msg1", Atomic "msg2", Atomic "msg3"],
    exampleCommunicationThreeMsg,
    Right $ LSend [(LAtom "X0", LNil), (LAtom "X1", LNil), (LAtom "X2", LNil)]
  )

testCommunicationThreeMsgB :: TestCaseDataCommunication
testCommunicationThreeMsgB =
  let x0x3 = LIf (LAtom "X0") (LAtom "X3")
      x1x3 = LIf (LAtom "X1") (LAtom "X3")
      x2x3 = LIf (LAtom "X2") (LAtom "X3")
      unlock = LUnlock LNil
      lockunlock = LUnlock . LLock $ unlock
      ifs = x0x3 (x1x3 unlock (x2x3 unlock lockunlock)) (x1x3 (x2x3 unlock lockunlock) (x2x3 lockunlock unlock))
      expected = LReceive "X3" $ LLock ifs
   in ( "B",
        "three messages",
        [Atomic "msg1", Atomic "msg2", Atomic "msg3"],
        exampleCommunicationThreeMsg,
        Right expected
      )

testCommunicationThreeMsgBNoKnowledge :: TestCaseDataCommunication
testCommunicationThreeMsgBNoKnowledge =
  ( "B",
    "three messages, no knowledge",
    [],
    exampleCommunicationThreeMsg,
    Right . LReceive "X0" . LLock $ LUnlock LNil
  )

-- COMMUNICATION -- Example: multiple checks --

exampleCommunicationMultipleChecks :: Choreography
exampleCommunicationMultipleChecks =
  let interaction1 c = Interaction "B" "A" [(Atomic "msg1", c)] Epsilon
      interaction2 c = Interaction "A" "B" [(Atomic "msg2", c)] Epsilon
      interaction3 c = Interaction "B" "A" [(Atomic "msg3", c)] Epsilon
   in interaction1 . interaction2 . interaction3 $ Nil

testCommunicationMultipleChecksA :: TestCaseDataCommunication
testCommunicationMultipleChecksA =
  let expected =
        LReceive "X3"
          . LLock
          $ LIf
            (LAtom "X0")
            (LAtom "X3")
            ( LUnlock $
                LSend
                  [ ( LAtom "X1",
                      LReceive "X4" . LLock $
                        LIf
                          (LAtom "X2")
                          (LAtom "X4")
                          (LUnlock LNil)
                          (LUnlock LNil)
                    )
                  ]
            )
            (LUnlock LNil)
   in ( "A",
        "multiple checks",
        [Atomic "msg1", Atomic "msg2", Atomic "msg3"],
        exampleCommunicationMultipleChecks,
        Right expected
      )

-- COMMUNICATION -- Example: default --

testCommunicationDefault :: TestCaseDataCommunication
testCommunicationDefault =
  let choreo = Interaction "A" "B" [(Atomic "m", Nil)] (Otherwise . Lock "B" $ Unlock Nil)
      expected = LReceive "X1" . LLock $ LIf (LAtom "X0") (LAtom "X1") (LUnlock LNil) (LUnlock . LLock $ LUnlock LNil)
   in ("B", "default 1", [Atomic "m"], choreo, Right expected)

-- COMMUNICATION -- Example: crypto --

exampleCommunicationCrypto :: Choreography
exampleCommunicationCrypto =
  let skAB = Composed (UnDef "sk") [Atomic "A", Atomic "B"]
      pkB = Composed (UnDef "pk") [Atomic "B"]
      scrypt = Composed SCRYPT [skAB, Atomic "K", Atomic "r1"]
      crypt = Composed CRYPT [pkB, Atomic "N", Atomic "r2"]
   in Interaction
        "A"
        "B"
        [ (scrypt, Interaction "B" "A" [(Composed (UnDef "h") [Atomic "K"], Nil)] Epsilon),
          (crypt, Interaction "B" "A" [(Atomic "N", Nil)] Epsilon)
        ]
        Epsilon

testCommunicationCryptoA :: TestCaseDataCommunication
testCommunicationCryptoA =
  let scrypt = LComp SCRYPT [LAtom "X0", LAtom "X1", LAtom "X5"]
      crypt = LComp CRYPT [LAtom "X2", LAtom "X3", LAtom "X6"]
      knowledge =
        [ Composed (UnDef "sk") [Atomic "A", Atomic "B"],
          Atomic "K",
          Composed (UnDef "pk") [Atomic "B"],
          Atomic "N",
          Composed (UnDef "h") [Atomic "K"],
          Atomic "r1",
          Atomic "r2"
        ]
      expected =
        LSend
          [ (scrypt, LReceive "X7" . LLock $ LIf (LAtom "X4") (LAtom "X7") (LUnlock LNil) (LUnlock LNil)),
            (crypt, LReceive "X7" . LLock $ LIf (LAtom "X3") (LAtom "X7") (LUnlock LNil) (LUnlock LNil))
          ]
   in ( "A",
        "crypto",
        knowledge,
        exampleCommunicationCrypto,
        Right expected
      )

testCommunicationAfterLockA :: TestCaseDataCommunication
testCommunicationAfterLockA =
  let example = Lock "A" . Nonce "X" . Unlock $ Interaction "A" "B" [(Atomic "X", Nil)] Epsilon
      expected = LLock . LNew "X0" . LUnlock $ LSend [(LAtom "X0", LNil)]
   in ("A", "after lock", [], example, Right expected)

testCommunicationAfterLockB :: TestCaseDataCommunication
testCommunicationAfterLockB =
  let example = Lock "A" . Nonce "X" . Unlock $ Interaction "A" "B" [(Atomic "X", Nil)] Epsilon
      expected = LReceive "X0" LNil
   in ("B", "after lock", [], example, Right expected)

testCommunicationSendReceived :: TestCaseDataCommunication
testCommunicationSendReceived =
  let example = Interaction "A" "B" [(Atomic "msg", Interaction "B" "A" [(Atomic "msg", Nil)] Epsilon)] Epsilon
      expected = LReceive "X0" $ LSend [(LAtom "X0", LNil)]
   in ("B", "send received", [], example, Right expected)

testCommunicationSendReceivedScrypt :: TestCaseDataCommunication
testCommunicationSendReceivedScrypt =
  let example =
        Interaction
          "A"
          "B"
          [ ( Composed SCRYPT [Atomic "K", Atomic "msg", Atomic "r"],
              Interaction "B" "A" [(Atomic "msg", Nil)] Epsilon
            )
          ]
          Epsilon
      expected =
        LReceive "X1" . LLock $
          LTry
            "X2"
            DSCRYPT
            [LAtom "X0", LAtom "X1"]
            (LUnlock $ LSend [(LAtom "X2", LNil)])
            (LUnlock LNil)
   in ("B", "send received scrypt", [Atomic "K"], example, Right expected)

testCommunicationSendReceivedScrypt2 :: TestCaseDataCommunication
testCommunicationSendReceivedScrypt2 =
  let example =
        Interaction
          "A"
          "B"
          [ ( Composed SCRYPT [Composed (UnDef "sk") [Atomic "A", Atomic "B"], Atomic "msg", Atomic "r"],
              Interaction "B" "A" [(Atomic "msg", Nil)] Epsilon
            )
          ]
          Epsilon
      expected =
        LReceive "X1" . LLock $
          LTry
            "X2"
            DSCRYPT
            [LAtom "X0", LAtom "X1"]
            (LUnlock $ LSend [(LAtom "X2", LNil)])
            (LUnlock LNil)
   in ("B", "send received scrypt 2", [Composed (UnDef "sk") [Atomic "A", Atomic "B"]], example, Right expected)

testCommunicationSendReceivedCrypt :: TestCaseDataCommunication
testCommunicationSendReceivedCrypt =
  let example =
        Interaction
          "A"
          "B"
          [ ( Composed CRYPT [Atomic "K", Atomic "msg", Atomic "r"],
              Interaction "B" "A" [(Atomic "msg", Nil)] Epsilon
            )
          ]
          Epsilon
      expected =
        LReceive
          "X1"
          ( LLock
              ( LTry
                  "X2"
                  PUBK
                  [LAtom "X0"]
                  ( LTry
                      "X3"
                      DCRYPT
                      [LAtom "X0", LAtom "X1"]
                      (LUnlock (LSend [(LAtom "X3", LNil)]))
                      (LUnlock LNil)
                  )
                  (LUnlock LNil)
              )
          )
   in ("B", "send received crypt", [Composed INV [Atomic "K"]], example, Right expected)

testCommunicationSendReceivedPair :: TestCaseDataCommunication
testCommunicationSendReceivedPair =
  let example =
        Interaction
          "A"
          "B"
          [ ( Composed PAIR [Atomic "x", Atomic "y"],
              Interaction
                "B"
                "A"
                [(Composed PAIR [Atomic "x", Atomic "z"], Nil)]
                Epsilon
            )
          ]
          Epsilon
      expected =
        LReceive "X1" . LLock $
          LTry
            "X2"
            PROJ1
            [LAtom "X1"]
            ( LTry
                "X3"
                PROJ2
                [LAtom "X1"]
                (LUnlock $ LSend [(LComp PAIR [LAtom "X2", LAtom "X0"], LNil)])
                (LUnlock LNil)
            )
            (LUnlock LNil)
   in ("B", "send received pair", [Atomic "z"], example, Right expected)

testCommunicationSendReceivedPairPair :: TestCaseDataCommunication
testCommunicationSendReceivedPairPair =
  let example =
        Interaction
          "A"
          "B"
          [ ( Composed PAIR [Composed PAIR [Atomic "x", Atomic "y"], Atomic "z"],
              Interaction
                "B"
                "A"
                [(Composed PAIR [Atomic "x", Composed PAIR [Atomic "y", Atomic "z"]], Nil)]
                Epsilon
            )
          ]
          Epsilon
      expected =
        LReceive "X0" . LLock $
          LTry
            "X1"
            PROJ1
            [LAtom "X0"]
            ( LTry
                "X2"
                PROJ2
                [LAtom "X0"]
                ( LTry
                    "X3"
                    PROJ1
                    [LAtom "X1"]
                    ( LTry
                        "X4"
                        PROJ2
                        [LAtom "X1"]
                        (LUnlock $ LSend [(LComp PAIR [LAtom "X3", LComp PAIR [LAtom "X4", LAtom "X2"]], LNil)])
                        (LUnlock LNil)
                    )
                    (LUnlock LNil)
                )
                (LUnlock LNil)
            )
            (LUnlock LNil)
   in ("B", "send received pair pair", [], example, Right expected)

-- REWRITE -- HELPERS --

type TestCaseDataRewrite = (T.Text, String, [Term], Choreography, [(FUNCTIONS, RewriteRule)], TranslationResult LocalBehavior)

mkTestRewrite :: TestCaseDataRewrite -> TestTree
mkTestRewrite (agent, msg, frame, choreo, rewriteRules, expected) =
  testCase
    (msg ++ ", " ++ T.unpack agent)
    ( assertEqual
        ("Communication, " ++ msg)
        expected
        ( translateWith
            agent
            stdConstructors
            (Map.fromList rewriteRules)
            [(mkState $ RoleKnowledge frame [], choreo)]
        )
    )

-- REWRITE -- TESTS --

testRewriteSendReceivedSession :: TestCaseDataRewrite
testRewriteSendReceivedSession =
  let example =
        Interaction
          "A"
          "B"
          [ ( Composed (UnDef "session") [Atomic "x", Atomic "y"],
              Interaction
                "B"
                "A"
                [(Composed PAIR [Atomic "y", Atomic "x"], Nil)]
                Epsilon
            )
          ]
          Epsilon
      expected =
        LReceive "X0" . LLock $
          LTry
            "X1"
            (UnDef "sfst")
            [LAtom "X0"]
            ( LTry
                "X2"
                (UnDef "ssnd")
                [LAtom "X0"]
                ( LUnlock $
                    LSend
                      [ (LComp PAIR [LAtom "X2", LAtom "X1"], LNil)
                      ]
                )
                (LUnlock LNil)
            )
            (LUnlock LNil)
      rewriteRules =
        [ ( UnDef "sfst",
            ( [ RR.Comp
                  (UnDef "session")
                  [ RR.RewriteVar (RR.UnDef "x"),
                    RR.RewriteVar (RR.UnDef "y")
                  ]
              ],
              RR.RewriteVar (RR.UnDef "x")
            )
          ),
          ( UnDef "ssnd",
            ( [ RR.Comp
                  (UnDef "session")
                  [ RR.RewriteVar (RR.UnDef "x"),
                    RR.RewriteVar (RR.UnDef "y")
                  ]
              ],
              RR.RewriteVar (RR.UnDef "y")
            )
          )
        ]
   in ("B", "send received session", [], example, rewriteRules, Right expected)

-- EXAMPLES --

testExampleBACprotocolC :: TestCaseDataCommunication
testExampleBACprotocolC =
  let knowledge = [Composed (UnDef "sk") [Atomic "x"], Atomic "fixedR", Atomic "ok", Atomic "formatErr"]
   in ("C", "Example BAC", knowledge, protocolBAC, Right LNil)


mkDescription :: Agent -> Description
mkDescription ag =
  Description
    { agent = ag,
      constructors = stdConstructors,
      rewriteRules = stdRewriteRules
    }