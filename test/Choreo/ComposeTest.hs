{-# LANGUAGE OverloadedStrings #-}

module Choreo.ComposeTest (tests) where

import Types.Choreography (Term (..))
import Compiler.ToLocalBehavior.RecipeUtility (combineRecipes, composeSet)
import Types.Simple (FUNCTIONS (..))
import Types.LocalBehavior (Recipe (..))
import Choreography.State (mkState)
import qualified Data.Set as Set
import Types.ChoreographyProtocolShell (RoleKnowledge (RoleKnowledge))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)
import Syntax.Util (stdConstructors)

type TestCaseData = (Term, [Term], [Recipe])

tests :: TestTree
tests =
  testGroup
    "Compose Tests"
    $ testCombineRecipes
      : map
        mkTest
        [ testComposeScrypt,
          testComposeCrypt,
          testComposeSign,
          testComposeScryptDouble,
          testComposePair
        ]

mkTest :: TestCaseData -> TestTree
mkTest (term, knowledge, expected) =
  testCase
    (show term)
    ( assertEqual
        ("Compose: " ++ show term)
        (Set.fromList expected)
        (composeSet stdConstructors (mkState (RoleKnowledge knowledge [])) term)
    )

-- COMPOSE --

testCombineRecipes :: TestTree
testCombineRecipes =
  testCase "Combine Multiple Recipes" $
    let recipeOpt1 = Set.fromList [LAtom "x", LAtom "y"]
        recipeOpt2 = Set.fromList [LComp SCRYPT [LAtom "k", LAtom "m"], LAtom "X5"]
        recipeOpt3 = Set.fromList [LAtom "end"]
        expectedResult =
          Set.fromList
            [ [LAtom "x", LComp SCRYPT [LAtom "k", LAtom "m"], LAtom "end"],
              [LAtom "y", LComp SCRYPT [LAtom "k", LAtom "m"], LAtom "end"],
              [LAtom "x", LAtom "X5", LAtom "end"],
              [LAtom "y", LAtom "X5", LAtom "end"]
            ]
     in assertEqual
          "Combine multiple recipes"
          expectedResult
          ( combineRecipes
              [recipeOpt1, recipeOpt2, recipeOpt3]
          )

testComposeScrypt :: TestCaseData
testComposeScrypt =
  let term = Composed SCRYPT [Atomic "k", Atomic "m", Atomic "r"]
      knowledge = [Atomic "k", Atomic "m", Atomic "r", term]
      expected = [LAtom "X3", LComp SCRYPT [LAtom "X0", LAtom "X1", LAtom "X2"]]
   in (term, knowledge, expected)

testComposeCrypt :: TestCaseData
testComposeCrypt =
  let term = Composed CRYPT [Atomic "k", Atomic "m", Atomic "r"]
      knowledge = [Atomic "k", Atomic "m", Atomic "r", term]
      expected = [LAtom "X3", LComp CRYPT [LAtom "X0", LAtom "X1", LAtom "X2"]]
   in (term, knowledge, expected)

testComposeSign :: TestCaseData
testComposeSign =
  let term = Composed SIGN [Composed  INV [Atomic "k"], Atomic "m"]
      knowledge = [Composed  INV [Atomic "k"], Atomic "m", term]
      expected = [LAtom "X2", LComp SIGN [LAtom "X0", LAtom "X1"]]
   in (term, knowledge, expected)

testComposeScryptDouble :: TestCaseData
testComposeScryptDouble =
  let term = Composed SCRYPT [Atomic "k2", Composed SCRYPT [Atomic "k1", Atomic "m", Atomic "r1"], Atomic "r2"]
      knowledge =
        [ Atomic "k1",
          Atomic "k2",
          term,
          Composed SCRYPT [Atomic "k1", Atomic "m", Atomic "r1"],
          Atomic "m",
          Atomic "r1",
          Atomic "r2"
        ]
      expected =
        [ LAtom "X2",
          LComp SCRYPT [LAtom "X1", LAtom "X3", LAtom "X6"],
          LComp SCRYPT [LAtom "X1", LComp SCRYPT [LAtom "X0", LAtom "X4", LAtom "X5"], LAtom "X6"]
        ]
   in (term, knowledge, expected)

testComposePair :: TestCaseData
testComposePair =
  let term = Composed PAIR [Atomic "p1", Atomic "p2"]
      knowledge = [Atomic "p1", Atomic "p2", term]
      expected =
        [ LAtom "X2",
          LComp PAIR [LAtom "X0", LAtom "X1"]
        ]
   in (term, knowledge, expected)
