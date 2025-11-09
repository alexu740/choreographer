{-# LANGUAGE OverloadedStrings #-}

module Choreo.AnalysisTest (tests) where

import Compiler.ToLocalBehavior.TermRewriter (analyzePhase1State)
import Compiler.ToLocalBehavior.CheckGenerator (analyzePhase2State, similarChecks)
import Types.Rewrite (DestructorApp (..), Description(..), State(..))
import Types.Choreography (Agent, Term (..))
import Types.Simple (FUNCTIONS (..))
import Types.LocalBehavior (Recipe (..))
import Choreography.State (insertDestruction, mkState)
import qualified Choreography.State as State
import Data.Map as Map (elems)
import Data.Set as Set (fromList)
import Syntax.Util (stdConstructors)
import Choreography.Enricher (stdRewriteRules)
import Types.ChoreographyProtocolShell (RoleKnowledge (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)


type TestCaseDataFrame = (String, [Term], [Term])

type TestCaseDataDestructors = (String, [Term], [DestructorApp])

type TestCaseDataChecks = (String, [Term], [(Recipe, Recipe)])

tests :: TestTree
tests =
  testGroup
    "Analysis Tests"
    [ testGroup "Phase 1: frame" $
        map
          mkTestPhase1Frame
          [ testAnalysisFrameScrypt,
            testAnalysisFrameCrypt,
            testAnalysisFrameSign,
            testAnalysisFramePair,
            testAnalysisFrameScryptDouble,
            testAnalysisFrameScryptTriple,
            testAnalysisFrameComplex,
            testAnalysisFrameUnDefnownHash
          ],
      testGroup "Phase 1: destructors" $
        map
          mkTestPhase1Destructors
          [ testAnalysisDestructorsScrypt,
            testAnalysisDestructorsCrypt,
            testAnalysisDestructorsSign,
            testAnalysisDestructorsPair,
            testAnalysisDestructorsScryptDouble,
            testAnalysisDestructorsScryptTriple,
            testAnalysisDestructorsComplex,
            testAnalysisDestructorsUnDefnownHash
          ]
          ++ [testAnalysisDestructorsKnownDscrypt],
      testGroup "Checks" $
        map
          mkTestPhase2Checks
          [ testAnalysisChecksScrypt,
            testAnalysisChecksCrypt,
            testAnalysisChecksSign,
            testAnalysisChecksPair,
            testAnalysisChecksScryptDouble,
            testAnalysisChecksScryptTriple,
            testAnalysisChecksComplex,
            testAnalysisChecksUnDefnownHash
          ]
          ++ [testAnalysisChecksNoNew],
      testGroup "Helpers" [testSimilarChecks]
    ]

mkTestPhase1Frame :: TestCaseDataFrame -> TestTree
mkTestPhase1Frame (msg, knowledge, expectedFrame) =
  testCase msg $
    let roleK = RoleKnowledge knowledge []
        description = mkDescription "DUMMY"
        (state, _) = analyzePhase1State (length knowledge) description (mkState roleK)
        frameRes = frame state
     in assertEqual
          ("Analyse frame: " ++ msg)
          (Set.fromList expectedFrame)
          (Set.fromList (Map.elems frameRes))

mkTestPhase1Destructors :: TestCaseDataDestructors -> TestTree
mkTestPhase1Destructors (msg, knowledge, expectedDestructors) =
  testCase msg $
    let roleK = RoleKnowledge knowledge []
        description = mkDescription "DUMMY"
        (_, destructorsRes) = analyzePhase1State (length knowledge) description (mkState roleK)
     in assertEqual
          ("Analyse destructors: " ++ msg)
          expectedDestructors
          destructorsRes

mkTestPhase2Checks :: TestCaseDataChecks -> TestTree
mkTestPhase2Checks (msg, knowledge, expectedChecks) =
  testCase msg $
    let roleK = RoleKnowledge knowledge []
        description = mkDescription "DUMMY"
        (_, checksRes) = analyzePhase2State description (mkState roleK)
     in assertEqual
          ("Analyse checks: " ++ msg)
          expectedChecks
          checksRes

-- ANALYSIS : FRAMES --

frameScrypt :: [Term]
frameScrypt =
  [ Composed SCRYPT [Atomic "k", Atomic "m", Atomic "r"],
    Atomic "k"
  ]

frameCrypt :: [Term]
frameCrypt =
  [ Composed CRYPT [Atomic "k", Atomic "m", Atomic "r"],
    Composed INV [Atomic "k"]
  ]

frameSign :: [Term]
frameSign =
  [ Composed SIGN [Composed INV [Atomic "k"], Atomic "m"],
    Atomic "k"
  ]

framePair :: [Term]
framePair =
  [Composed PAIR [Atomic "m1", Atomic "m2"]]

frameScryptDouble :: [Term]
frameScryptDouble =
  [ Composed SCRYPT [Atomic "k2", Composed SCRYPT [Atomic "k1", Atomic "m", Atomic "r1"], Atomic "r2"],
    Atomic "k2",
    Atomic "k1"
  ]

frameScryptTriple :: [Term]
frameScryptTriple =
  [ Atomic "k1",
    Atomic "k2",
    Atomic "k3",
    Composed
      SCRYPT
      [ Atomic "k3",
        Composed
          SCRYPT
          [ Atomic "k2",
            Composed SCRYPT [Atomic "k1", Atomic "m", Atomic "r1"],
            Atomic "r2"
          ],
        Atomic "r3"
      ]
  ]

frameComplex :: [Term]
frameComplex =
  [ Composed SIGN [Composed INV [Atomic "k2"], Composed CRYPT [Atomic "k1", Atomic "m", Atomic "r1"]],
    Atomic "k2",
    Atomic "k1",
    Composed INV [Atomic "k1"]
  ]

frameUnDefnownHash :: [Term]
frameUnDefnownHash =
  [ Composed (UnDef "hash") [Atomic "k1"],
    Atomic "k2",
    Composed SCRYPT [Atomic "k2", Atomic "msg", Atomic "r"]
  ]

frameKnownDscrypt :: [Term]
frameKnownDscrypt =
  [ Atomic "k1",
    Atomic "k2",
    Composed SCRYPT [Atomic "k1", Composed SCRYPT [Atomic "k2", Atomic "m", Atomic "r2"], Atomic "r1"],
    Composed SCRYPT [Atomic "k2", Atomic "m", Atomic "r2"],
    Atomic "m"
  ]

-- ANALYSIS : FRAME --

testAnalysisFrameScrypt :: TestCaseDataFrame
testAnalysisFrameScrypt =
  let knowledge = frameScrypt
      expectedFrame = Atomic "m" : knowledge
   in ("scrypt", knowledge, expectedFrame)

testAnalysisFrameCrypt :: TestCaseDataFrame
testAnalysisFrameCrypt =
  let knowledge = frameCrypt
      expectedFrame = Atomic "k" : Atomic "m" : knowledge
   in ("crypt", knowledge, expectedFrame)

testAnalysisFrameSign :: TestCaseDataFrame
testAnalysisFrameSign =
  let knowledge = frameSign
      expectedFrame = Atomic "m" : knowledge
   in ("sign", knowledge, expectedFrame)

testAnalysisFramePair :: TestCaseDataFrame
testAnalysisFramePair =
  let knowledge = framePair
      expectedFrame = Atomic "m1" : Atomic "m2" : knowledge
   in ("pair", knowledge, expectedFrame)

testAnalysisFrameScryptDouble :: TestCaseDataFrame
testAnalysisFrameScryptDouble =
  let knowledge = frameScryptDouble
      expectedFrame = [Atomic "m", Composed SCRYPT [Atomic "k1", Atomic "m", Atomic "r1"]] ++ knowledge
   in ("double scrypt", knowledge, expectedFrame)

testAnalysisFrameScryptTriple :: TestCaseDataFrame
testAnalysisFrameScryptTriple =
  let knowledge = frameScryptTriple
      expectedFrame =
        [ Atomic "m",
          Composed SCRYPT [Atomic "k1", Atomic "m", Atomic "r1"],
          Composed SCRYPT [Atomic "k2", Composed SCRYPT [Atomic "k1", Atomic "m", Atomic "r1"], Atomic "r2"]
        ]
          ++ knowledge
   in ("triple scrypt", knowledge, expectedFrame)

testAnalysisFrameComplex :: TestCaseDataFrame
testAnalysisFrameComplex =
  let knowledge = frameComplex
      expectedFrame =
        [ Atomic "m",
          Composed CRYPT [Atomic "k1", Atomic "m", Atomic "r1"]
        ]
          ++ knowledge
   in ("complex", knowledge, expectedFrame)

testAnalysisFrameUnDefnownHash :: TestCaseDataFrame
testAnalysisFrameUnDefnownHash =
  let knowledge = frameUnDefnownHash
      expectedFrame =
        Atomic "msg" : knowledge
   in ("UnDefnown hash", knowledge, expectedFrame)

-- ANALYSIS : DESTRUCTORS --

testAnalysisDestructorsScrypt :: TestCaseDataDestructors
testAnalysisDestructorsScrypt =
  let expectedDestructors =
        [ DestructorApp
            { dlabel = "X2",
              ddestructor = DSCRYPT,
              dsubterms = [LAtom "X1", LAtom "X0"]
            }
        ]
   in ("scrypt", frameScrypt, expectedDestructors)

testAnalysisDestructorsCrypt :: TestCaseDataDestructors
testAnalysisDestructorsCrypt =
  let expectedDestructors =
        [ DestructorApp
            { dlabel = "X2",
              ddestructor = DCRYPT,
              dsubterms = [LAtom "X1", LAtom "X0"]
            },
          DestructorApp
            { dlabel = "X3",
              ddestructor = PUBK,
              dsubterms = [LAtom "X1"]
            }
        ]
   in ("crypt", frameCrypt, expectedDestructors)

testAnalysisDestructorsSign :: TestCaseDataDestructors
testAnalysisDestructorsSign =
  let expectedDestructors =
        [ DestructorApp
            { dlabel = "X2",
              ddestructor = OPEN,
              dsubterms = [LAtom "X1", LAtom "X0"]
            }
        ]
   in ("sign", frameSign, expectedDestructors)

testAnalysisDestructorsPair :: TestCaseDataDestructors
testAnalysisDestructorsPair =
  let expectedDestructors =
        [ DestructorApp
            { dlabel = "X1",
              ddestructor = PROJ1,
              dsubterms = [LAtom "X0"]
            },
          DestructorApp
            { dlabel = "X2",
              ddestructor = PROJ2,
              dsubterms = [LAtom "X0"]
            }
        ]
   in ("pair", framePair, expectedDestructors)

testAnalysisDestructorsScryptDouble :: TestCaseDataDestructors
testAnalysisDestructorsScryptDouble =
  let expectedDestructors =
        [ DestructorApp
            { dlabel = "X3",
              ddestructor = DSCRYPT,
              dsubterms = [LAtom "X1", LAtom "X0"]
            },
          DestructorApp
            { dlabel = "X4",
              ddestructor = DSCRYPT,
              dsubterms = [LAtom "X2", LAtom "X3"]
            }
        ]
   in ("double scrypt", frameScryptDouble, expectedDestructors)

testAnalysisDestructorsScryptTriple :: TestCaseDataDestructors
testAnalysisDestructorsScryptTriple =
  let expectedDestructors =
        [ DestructorApp
            { dlabel = "X4",
              ddestructor = DSCRYPT,
              dsubterms = [LAtom "X2", LAtom "X3"]
            },
          DestructorApp
            { dlabel = "X5",
              ddestructor = DSCRYPT,
              dsubterms = [LAtom "X1", LAtom "X4"]
            },
          DestructorApp
            { dlabel = "X6",
              ddestructor = DSCRYPT,
              dsubterms = [LAtom "X0", LAtom "X5"]
            }
        ]
   in ("triple scrypt", frameScryptTriple, expectedDestructors)

testAnalysisDestructorsComplex :: TestCaseDataDestructors
testAnalysisDestructorsComplex =
  let expectedDestructors =
        [ DestructorApp
            { dlabel = "X4",
              ddestructor = OPEN,
              dsubterms = [LAtom "X1", LAtom "X0"]
            },
          DestructorApp
            { dlabel = "X5",
              ddestructor = DCRYPT,
              dsubterms = [LAtom "X3", LAtom "X4"]
            },
          DestructorApp
            { dlabel = "X6",
              ddestructor = PUBK,
              dsubterms = [LAtom "X3"]
            }
        ]
   in ("complex", frameComplex, expectedDestructors)

testAnalysisDestructorsUnDefnownHash :: TestCaseDataDestructors
testAnalysisDestructorsUnDefnownHash =
  let expectedDestructors =
        [ DestructorApp
            { dlabel = "X3",
              ddestructor = DSCRYPT,
              dsubterms = [LAtom "X1", LAtom "X2"]
            }
        ]
   in ("UnDefnown hash", frameUnDefnownHash, expectedDestructors)

testAnalysisDestructorsKnownDscrypt :: TestTree
testAnalysisDestructorsKnownDscrypt =
  let msg = "Known Dscrypt"
   in testCase msg $
        let description = mkDescription "DUMMY"
            state = insertDestruction "X3" . insertDestruction "X2" . mkState $ RoleKnowledge frameKnownDscrypt []
            (_, destructorsRes) = analyzePhase1State (length frameKnownDscrypt) description state
         in assertEqual
              ("Analyse destructors: " ++ msg)
              []
              destructorsRes

-- ANALYSIS : CHECKS --

testAnalysisChecksScrypt :: TestCaseDataChecks
testAnalysisChecksScrypt = ("scrypt", frameScrypt, [])

testAnalysisChecksCrypt :: TestCaseDataChecks
testAnalysisChecksCrypt = ("crypt", frameCrypt, [])

testAnalysisChecksSign :: TestCaseDataChecks
testAnalysisChecksSign = ("sign", frameSign, [])

testAnalysisChecksPair :: TestCaseDataChecks
testAnalysisChecksPair = ("pair", framePair ++ [Atomic "m1", Atomic "m2"], [(LAtom "X0", LComp PAIR [LAtom "X1", LAtom "X2"])])

testAnalysisChecksScryptDouble :: TestCaseDataChecks
testAnalysisChecksScryptDouble = ("double scrypt", frameScryptDouble, [])

testAnalysisChecksScryptTriple :: TestCaseDataChecks
testAnalysisChecksScryptTriple = ("triple scrypt", frameScryptTriple, [])

testAnalysisChecksComplex :: TestCaseDataChecks
testAnalysisChecksComplex =
  let expectedChecks =
        [ ( LComp
              VCRYPT
              [ LAtom "X3",
                LComp CRYPT [LAtom "X2", LAtom "__TRUE__"]
              ],
            LAtom "__TRUE__"
          )
        ]
   in ("complex", frameComplex, expectedChecks)

testAnalysisChecksUnDefnownHash :: TestCaseDataChecks
testAnalysisChecksUnDefnownHash = ("UnDefnown hash", frameUnDefnownHash, [])

testAnalysisChecksNoNew :: TestTree
testAnalysisChecksNoNew =
  testCase "No New" $
    let terms = map Atomic ["N", "N", "R", "R", "R"]
        description = mkDescription "DUMMY"
        (state, _) = analyzePhase2State description (mkState $ RoleKnowledge terms [])
        (_, checks) = analyzePhase2State description state
     in assertEqual
          ("Analyse checks: " ++ "No New")
          []
          checks

-- ANALYSIS : HELPERS --

testSimilarChecks :: TestTree
testSimilarChecks =
  testCase "Similar checks" $
    let terms = [Atomic "msg", Atomic "msg"]
     in assertEqual
          "Similar check 1"
          (similarChecks stdConstructors (mkState $ RoleKnowledge terms []) (Atomic "msg"))
          [(LAtom "X0", LAtom "X1")]

mkDescription :: Agent -> Description
mkDescription ag =
  Description
    { agent = ag,
      constructors = stdConstructors,
      rewriteRules = stdRewriteRules
    }