{-# LANGUAGE OverloadedStrings #-}
module Sapic.TermRewrite where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Data.Traversable (mapAccumL)

import Types.Sapic(SRecipe(..))
import Types.Simple (FUNCTIONS(..))
import Types.Choreography
  ( Choreography(..)
  , Term(..)
  , Atomic(..)
  , Agent
  , CDefault(..)
  )
import Compiler.ToSapicPlus.SFrame(SFrame(..))
import Compiler.ToSapicPlus.RewriteSystem.EquationalTheoryExtension(termIsComposableModuloTheory, findEquivalenceClass)
import Compiler.ToSapicPlus.RewriteSystem.RewriteSystem(initializeRewriteSystem)
import Compiler.ToSapicPlus.RecipeUtility(constructCommmonRecipe, compose) 
import qualified Control.Applicative as List
import Types.ChoreographyProtocolShell
  ( ProtocolDescription(..)
  , RoleInfo(..)
  , Sigma(..)
  , SecurityGoal(..)
  )

protoInteractionSimple :: ProtocolDescription
protoInteractionSimple =
  ProtocolDescription
    { protocolAlgebra = Map.empty,
      protocolCells = Map.empty,
      protocolSigma0 = Sigma {
              public = Map.empty,
              private = Map.empty,
              relation = Map.empty
            },
      protocolSigma = Sigma {
              public = Map.empty,
              private = Map.empty,
              relation = Map.empty
            },
      protocolRoles  = Map.fromList
        [ ("A", RoleInfo { roleKnowledge = [ Atomic "hello"
                                           , Composed PAIR [Atomic "x", Atomic "y"]
                                           ], roleChoice = Nothing
                         })
        , ("B", RoleInfo { roleKnowledge = [], roleChoice = Nothing })
        ]
    , protocolChoreo = Interaction "A" "B" [(Atomic "hello", Nil)] Epsilon
    , protocolGoals = List.empty
    }

tests :: TestTree
tests =
  testGroup
    "Term rewrite with equational theory extension"
    [ 
        unit_var_in_frame
        , unit_commutativity_class
        , unit_associativity_class
        , unit_exp_rewrite_class
        , unit_mult_composability_true
        , unit_mult_composability_false
        , unit_exp_composability_true
        , unit_recipe_siple
        , unit_recipe_common
        , unit_recipe_common_with_generator_func
        , unit_recipe_dh_composability
    ]

unit_var_in_frame :: TestTree
unit_var_in_frame =
  testCase "Variable in frame" $ do
    let frame = SFrame
          { mapping       = Map.fromList [("X1", Atomic "Na")]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    case initializeRewriteSystem protoInteractionSimple of
      Left err  -> assertFailure (T.unpack err)
      Right rs' -> do
        termIsComposableModuloTheory rs' frame (Atomic "Na") @?= True
        termIsComposableModuloTheory rs' frame (Atomic "Nb") @?= False
        findEquivalenceClass []  (Composed MULT [Atomic "Na", Atomic "Na"]) @?= [Composed MULT [Atomic "Na",Atomic "Na"]]
        termIsComposableModuloTheory rs' frame (Composed MULT [Atomic "Na", Atomic "Na"]) @?= True

unit_commutativity_class :: TestTree
unit_commutativity_class =
  testCase "Equiv class: MULT commutativity" $ do
    let t  = Composed MULT [Atomic "Na", Atomic "Nb"]
        t' = Composed MULT [Atomic "Nb", Atomic "Na"]
    findEquivalenceClass []  t @?= [t, t']

-- MULT associativity: mult(a, mult(b, c))  ~  mult(mult(a, b), c)
unit_associativity_class :: TestTree
unit_associativity_class =
  testCase "Equiv class: MULT associativity" $ do
    let tL  = Composed MULT [ Atomic "Na"
                            , Composed MULT [Atomic "Nb", Atomic "Nc"]
                            ]
        tR = [
          Composed MULT [Atomic "Na",Composed MULT [Atomic "Nb",Atomic "Nc"]],
          Composed MULT [Composed MULT [Atomic "Nb",Atomic "Nc"],Atomic "Na"],
          Composed MULT [Composed MULT [Atomic "Nc",Atomic "Nb"],Atomic "Na"],
          Composed MULT [Composed MULT [Atomic "Na",Atomic "Nb"],Atomic "Nc"],
          Composed MULT [Composed MULT [Atomic "Nb",Atomic "Na"],Atomic "Nc"],
          Composed MULT [Atomic "Na",Composed MULT [Atomic "Nc",Atomic "Nb"]],
          Composed MULT [Atomic "Nb",Composed MULT [Atomic "Nc",Atomic "Na"]],
          Composed MULT [Atomic "Nb",Composed MULT [Atomic "Na",Atomic "Nc"]],
          Composed MULT [Atomic "Nc",Composed MULT [Atomic "Nb",Atomic "Na"]],
          Composed MULT [Atomic "Nc",Composed MULT [Atomic "Na",Atomic "Nb"]],
          Composed MULT [Composed MULT [Atomic "Na",Atomic "Nc"],Atomic "Nb"],
          Composed MULT [Composed MULT [Atomic "Nc",Atomic "Na"],Atomic "Nb"]
          ]
    findEquivalenceClass []  tL @?= tR

-- EXP rewrite: exp(exp(x,a), b) = exp(x, mult(a,b))
unit_exp_rewrite_class :: TestTree
unit_exp_rewrite_class =
  testCase "Equiv class: EXP-nesting rewrite" $ do
    let g  = Atomic "g"
        a  = Atomic "Na"
        b  = Atomic "Nb"
        t  = Composed EXP [ Composed EXP [ g, a ]
                          , b
                          ]
        t' = Composed EXP [ g
                          , Composed MULT [ a, b ]
                          ]
    findEquivalenceClass []  t @?= [Composed EXP [Composed EXP [Atomic "g",Atomic "Na"],Atomic "Nb"],Composed EXP [Atomic "g",Composed MULT [Atomic "Na",Atomic "Nb"]],Composed EXP [Atomic "g",Composed MULT [Atomic "Nb",Atomic "Na"]],Composed EXP [Composed EXP [Atomic "g",Atomic "Nb"],Atomic "Na"]]

-- MULT compose: both args in frame => True (constructor allowed, args composable)
unit_mult_composability_true :: TestTree
unit_mult_composability_true =
  testCase "Composable: MULT when both args composable" $ do
    let frame = SFrame
          { mapping       = Map.fromList [("X1", Atomic "Na"), ("X2", Atomic "Nb")]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    case initializeRewriteSystem protoInteractionSimple of
      Left err  -> assertFailure (T.unpack err)
      Right rs' -> do
        termIsComposableModuloTheory rs' frame (Composed MULT [Atomic "Na", Atomic "Nb"]) @?= True

-- MULT compose: second arg NOT in frame => False
unit_mult_composability_false :: TestTree
unit_mult_composability_false =
  testCase "Not composable: MULT when one arg missing" $ do
    let frame = SFrame
          { mapping       = Map.fromList [("X1", Atomic "Na")]  -- Nb missing
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    case initializeRewriteSystem protoInteractionSimple of
      Left err  -> assertFailure (T.unpack err)
      Right rs' -> do
        termIsComposableModuloTheory rs' frame (Composed MULT [Atomic "Na", Atomic "Nb"]) @?= False

-- EXP compose: exp(exp(g,Na), Nb) is composable if g, Na, Nb are composable
unit_exp_composability_true :: TestTree
unit_exp_composability_true =
  testCase "Composable: EXP when all args composable" $ do
    let frame = SFrame
          { mapping       = Map.fromList [ ("Xg", Atomic "g")
                                         , ("Xa", Atomic "Na")
                                         , ("Xb", Atomic "Nb")
                                         ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
        term = Composed EXP [ Composed EXP [Atomic "g", Atomic "Na"]
                            , Atomic "Nb"
                            ]
    case initializeRewriteSystem protoInteractionSimple of
      Left err  -> assertFailure (T.unpack err)
      Right rs' -> do
        -- Direct structure requires g,Na,Nb composable -> True
        termIsComposableModuloTheory rs' frame term @?= True
---------
---------
unit_recipe_siple :: TestTree
unit_recipe_siple =
  testCase "Recipe construction for terms built on operations" $ do
    let frame1 = SFrame
          { mapping       = Map.fromList [ ("X1", Composed MULT [Atomic "Na", Atomic "Nb"]) ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }

    -- Frame with associativity example: X3 = mult(mult(Na, Nb), Nc)
    let frameAssoc = frame1
          { mapping = Map.union (mapping frame1)
                      (Map.fromList
                        [ ("X3", Composed MULT
                                  [ Composed MULT [Atomic "Na", Atomic "Nb"]
                                  , Atomic "Nc"
                                  ])
                        ])
          }

    -- Frame with DH example: X2 = exp(g, mult(Na, Nb))
    let frameDH = frameAssoc
          { mapping = Map.union (mapping frameAssoc)
                      (Map.fromList
                        [ ("X2", Composed EXP
                                  [ Atomic "g"
                                  , Composed MULT [Atomic "Na", Atomic "Nb"]
                                  ])
                        ])
          }

    let frameNested = frame1
          { mapping = Map.union (mapping frameAssoc)
                      (Map.fromList
                        [ 
                          ("X2", Atomic "g")
                        ])
          }

    -- 1) MULT commutativity: mult(Nb, Na) ~ mult(Na, Nb) => X1
    let q1 = Composed MULT [Atomic "Nb", Atomic "Na"]
    case compose protoInteractionSimple frame1 q1 of
      Nothing  -> assertFailure "No recipe for commutativity (q1)"
      Just r   -> r @?= RVariable "X1"

    -- 2) MULT identity (same order): mult(Na, Nb) => X1
    let q2 = Composed MULT [Atomic "Na", Atomic "Nb"]
    case compose protoInteractionSimple frame1 q2 of
      Nothing  -> assertFailure "No recipe for same-order MULT (q2)"
      Just r   -> r @?= RVariable "X1"

    -- 3) MULT associativity (right-nested ~ left-nested): mult(Na, mult(Nb, Nc)) => X3
    let q3 = Composed MULT [ Atomic "Na"
                           , Composed MULT [Atomic "Nb", Atomic "Nc"]
                           ]
    case compose protoInteractionSimple frameAssoc q3 of
      Nothing  -> assertFailure "No recipe for associativity (q3)"
      Just r   -> r @?= RVariable "X3"

    -- 4) EXP nesting rewrite: exp(exp(g, Na), Nb) ~ exp(g, mult(Na, Nb)) => X2
    let q4 = Composed EXP [ Composed EXP [Atomic "g", Atomic "Na"]
                          , Atomic "Nb"
                          ]
    case compose protoInteractionSimple frameDH q4 of
      Nothing  -> assertFailure "No recipe for DH nesting (q4)"
      Just r   -> r @?= RVariable "X2"

    -- 5) Negative: ask for exp(exp(g, Na), Nc) which is NOT in frameDH (Nb != Nc)
    let q5 = Composed EXP [ Composed EXP [Atomic "g", Atomic "Na"]
                          , Atomic "Nc"
                          ]
    case compose protoInteractionSimple frameDH q5 of
      Nothing -> pure ()
      Just r  -> assertFailure $ "Unexpected recipe for negative case (q5): " <> show r

    let q6 = Composed AENC
                        [ Composed MULT [Atomic "Nb", Atomic "Na"],
                          Atomic "g"
                        ]
    case compose protoInteractionSimple frameNested q6 of
      Nothing  -> assertFailure "No recipe for DH nesting (q6)"
      Just r   -> r @?= RFunction AENC [RVariable "X1",RVariable "X2"]


unit_recipe_common :: TestTree
unit_recipe_common =
  testCase "Common recipe construction for terms built on operations" $ do
    let frame1 = SFrame
          { mapping       = Map.fromList [ ("X1", Composed MULT [Atomic "Na", Atomic "Nb"]) ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }

    let frame2 = SFrame
          { mapping       = Map.fromList [ ("X1", Composed MULT [Atomic "Nb", Atomic "Na"]) ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    do
      let res = constructCommmonRecipe protoInteractionSimple
                 [ (frame1, Composed MULT [Atomic "Nb", Atomic "Na"])
                 , (frame2, Composed MULT [Atomic "Na", Atomic "Nb"])
                 ]
      case res of
        Left err  -> assertFailure (T.unpack err)
        Right r   -> r @?= RVariable "X1"

    let frameAssocA = SFrame
          { mapping       = Map.fromList
                              [ ("X1", Composed MULT [ Composed MULT [Atomic "Na", Atomic "Nb"]
                                                     , Atomic "Nc" ])
                              ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    let frameAssocB = SFrame
          { mapping       = Map.fromList
                              [ ("X1", Composed MULT [ Composed MULT [Atomic "Na", Atomic "Nb"]
                                                     , Atomic "Nc" ])
                              ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }

    -- 2) targetA = mult(Na, mult(Nb,Nc)) ; targetB = mult(mult(Na,Nb), Nc)
    do
      let targetA = Composed MULT [ Atomic "Na"
                                  , Composed MULT [Atomic "Nb", Atomic "Nc"] ]
          targetB = Composed MULT [ Composed MULT [Atomic "Na", Atomic "Nb"]
                                  , Atomic "Nc" ]
          res = constructCommmonRecipe protoInteractionSimple
                  [ (frameAssocA, targetA)
                  , (frameAssocB, targetB)
                  ]
      case res of
        Left err -> assertFailure (T.unpack err)
        Right r  -> r @?= RVariable "X1"

    -- Frames for DH rewrite: X1 = exp(g, mult(Na,Nb)) in both frames
    let frameDHA = SFrame
          { mapping       = Map.fromList
                              [ ("X1", Composed EXP [ Atomic "g"
                                                    , Composed MULT [Atomic "Na", Atomic "Nb"] ])
                              ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    let frameDHB = frameDHA

    -- 3) targetA = exp(exp(g,Na), Nb) ; targetB = exp(g, mult(Na,Nb))
    do
      let targetA = Composed EXP [ Composed EXP [Atomic "g", Atomic "Na"]
                                 , Atomic "Nb" ]
          targetB = Composed EXP [ Atomic "g"
                                 , Composed MULT [Atomic "Na", Atomic "Nb"] ]
          res = constructCommmonRecipe protoInteractionSimple
                  [ (frameDHA, targetA)
                  , (frameDHB, targetB)
                  ]
      case res of
        Left err -> assertFailure (T.unpack err)
        Right r  -> r @?= RVariable "X1"

    -- Frames for nested structure: X1 = pair(exp(g,mult(Na,Nb)), Z)
    let frameNestedA = SFrame
          { mapping       = Map.fromList
                              [ ("X1", Composed EXP [ Atomic "g", Composed MULT [Atomic "Na", Atomic "Nb"] ]),
                                ("X2", Atomic "g"),
                                ("X3", Atomic "Z"),
                                ("X4", Atomic "Na"),
                                ("X5", Atomic "Nb")
                              ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    let frameNestedB = frameNestedA

    -- 4) Nested: targetA = pair(exp(exp(g,Na),Nb), Z) targetB = pair(exp(g, mult(Na,Nb)), Z)
    do
      let targetA = Composed PAIR
                      [ Composed EXP [ Composed EXP [Atomic "g", Atomic "Na"], Atomic "Nb" ]
                      , Atomic "Z"
                      ]
          targetB = Composed PAIR
                      [ Composed EXP [ Atomic "g", Composed MULT [Atomic "Na", Atomic "Nb"] ]
                      , Atomic "Z"
                      ]
          res = constructCommmonRecipe protoInteractionSimple
                  [ (frameNestedA, targetA)
                  , (frameNestedB, targetB)
                  ]
      case res of
        Left err -> assertFailure (T.unpack err)
        Right r  -> r @?= RFunction PAIR [RVariable "X1", RVariable "X3"]

    let frameNegE = SFrame
          { mapping       = Map.fromList [ ("X1", Composed MULT [Atomic "Na", Atomic "Nb"]) ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    let frameNegF = SFrame
          { mapping       = Map.fromList [ ("X1", Composed MULT [Atomic "Na", Atomic "Nc"]) ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }

    do
      let res = constructCommmonRecipe protoInteractionSimple
                  [ (frameNegE, Composed MULT [Atomic "Na", Atomic "Nb"])
                  , (frameNegF, Composed MULT [Atomic "Na", Atomic "Nb"]) -- not equivalent in F
                  ]
      case res of
        Left _   -> pure ()  -- expected failure
        Right r  -> assertFailure $ "Unexpected common recipe in negative case: " <> show r


unit_recipe_common_with_generator_func :: TestTree
unit_recipe_common_with_generator_func =
  testCase "Common recipe with G" $ do
    let frame1 = SFrame
          { mapping       = Map.fromList [ ("X1", Atomic "Na") ]
          , receipts      = []
          , deconstructed = []
          , prevChecks    = []
          , bounded       = []
          , initial       = []
          }
    do
      let res = constructCommmonRecipe protoInteractionSimple
                 [ 
                    (frame1, Composed EXP [Composed G [],Atomic "Na"])
                 ]
      case res of
        Left err  -> assertFailure (T.unpack err)
        Right r   -> r @?= RFunction EXP [RFunction G [],RVariable "X1"]

unit_recipe_dh_composability :: TestTree
unit_recipe_dh_composability =
  testCase "Composability DH" $ do
    let frame = SFrame {
      mapping = Map.fromList [("X0",Composed EXP [Composed G [],Atomic "Na"]),("X1",Atomic "Nb"),("X2",Composed SENC [Atomic "MESS",Composed EXP [Composed EXP [Composed G [],Atomic "Nb"],Atomic "Na"]])]
    , deconstructed = []
    , bounded = []
    , receipts = []
    , prevChecks = []
    , initial = []
    }
    case initializeRewriteSystem protoInteractionSimple of
      Left err  -> assertFailure (T.unpack err)
      Right rs' -> do
        termIsComposableModuloTheory rs' frame (Composed EXP [Composed EXP [Composed G [],Atomic "Nb"],Atomic "Na"]) @?= True
        let recip = compose protoInteractionSimple frame (Composed EXP [Composed EXP [Composed G [],Atomic "Nb"],Atomic "Na"]) 
        case recip of 
          Just rec -> rec @?= RFunction EXP [RVariable "X0",RVariable "X1"]
          Nothing -> assertFailure "Nothing"