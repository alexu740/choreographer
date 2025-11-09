{-# LANGUAGE OverloadedStrings #-}
module Sapic.TranslationWithEquationalOperators where

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
import Compiler.ToSapicPlus.PrettyPrinter
import Compiler.ToSapicPlus.Translation
  ( translateChoreographyToSapicProcess
  , createInitialFrameChoreographyPair,
  translateAgent,
  translateProtocol,
  translateProcessBody
  )

protoDH :: ProtocolDescription
protoDH =
  ProtocolDescription
    { protocolAlgebra = Map.empty
    , protocolCells   = Map.empty
    , protocolSigma0  = Sigma { public = Map.empty, private = Map.empty, relation = Map.empty }
    , protocolSigma   = Sigma { public = Map.empty, private = Map.empty, relation = Map.empty }
    , protocolRoles   = Map.fromList
        [ ( "A"
          , RoleInfo
              { roleKnowledge = []
              , roleChoice    = Nothing
              }
          )
        , ( "B"
          , RoleInfo
              { roleKnowledge = []
              , roleChoice    = Nothing
              }
          )
        ]
    , protocolChoreo  =
        Lock "A" (Nonce "Na" (Unlock (
          Interaction "A" "B"
            [ ( 
                Composed EXP [Composed G [], Atomic "Na"],
                Lock "B" (Nonce "Nb" (Unlock (
                  Interaction "B" "A"
                    [ ( Composed EXP [Composed G [], Atomic "Nb"]
                      ,
                      Lock "A" (Nonce "MESS" (Unlock(
                        Interaction "A" "B" [
                          (
                            Composed SENC [Atomic "MESS", Composed EXP [Composed EXP [Composed G [], Atomic "Nb"], Atomic "Na"]],
                            Interaction "B" "A" [
                                (Atomic "MESS",
                                Nil)
                            ] Epsilon
                          )
                        ] Epsilon
                      )))
                      )
                    ] Epsilon
                )))
              )
            ] Epsilon
        )))
    , protocolGoals = []
    }

protoMult :: ProtocolDescription
protoMult =
  ProtocolDescription
    { protocolAlgebra = Map.empty
    , protocolCells   = Map.empty
    , protocolSigma0  = Sigma { public = Map.empty, private = Map.empty, relation = Map.empty }
    , protocolSigma   = Sigma { public = Map.empty, private = Map.empty, relation = Map.empty }
    , protocolRoles   = Map.fromList
        [ ( "A"
          , RoleInfo
              { roleKnowledge = []
              , roleChoice    = Nothing
              }
          )
        , ( "B"
          , RoleInfo
              { roleKnowledge = []
              , roleChoice    = Nothing
              }
          )
        ]
    , protocolChoreo  =
        Lock "A" (
          Nonce "Na" (
            Nonce "Nb" (
              Nonce "Nc" (
              Unlock (
                Interaction "A" "B"
                  [ ( Composed PAIR [ Composed PAIR [Atomic "Na", Atomic "Nb"], Composed PAIR [Atomic "Nc", Composed MULT [ Composed MULT [Atomic "Na", Atomic "Nb"], Atomic "Nc"]]]
                    , Lock "B" (
                        Unlock (
                          Interaction "B" "A"
                            [ ( Composed MULT [ Composed MULT [Atomic "Na", Atomic "Nb"], Atomic "Nc"]
                              , Lock "A" (
                                  Nonce "MESS" (
                                    Unlock (
                                      Interaction "A" "B"
                                        [ (Composed PAIR [Atomic "MESS", Composed MULT [Atomic "Na", Atomic "MESS"]], Nil) ]
                                        Epsilon
                                    )
                                  )
                                )
                              )
                            ]
                            Epsilon
                        )
                      )
                    )
                  ]
                  Epsilon
              )
            )
            )
          )
        )
    , protocolGoals = []
    }
    
protoExp1 :: ProtocolDescription
protoExp1 =
  ProtocolDescription
    { protocolAlgebra = Map.empty
    , protocolCells   = Map.empty
    , protocolSigma0  = Sigma { public = Map.empty, private = Map.empty, relation = Map.empty }
    , protocolSigma   = Sigma { public = Map.empty, private = Map.empty, relation = Map.empty }
    , protocolRoles   = Map.fromList
        [ ( "A"
          , RoleInfo
              { roleKnowledge = []
              , roleChoice    = Nothing
              }
          )
        , ( "B"
          , RoleInfo
              { roleKnowledge = []
              , roleChoice    = Nothing
              }
          )
        ]
    , protocolChoreo  =
        Lock "A" (
          Nonce "Na" (
            Nonce "Nb" (
              Nonce "Nc" (
              Unlock (
                Interaction "A" "B"
                  [ ( Composed PAIR [ Composed PAIR [Atomic "Na", Atomic "Nb"], Composed PAIR [Atomic "Nc", Composed MULT [ Composed MULT [Atomic "Na", Atomic "Nb"], Atomic "Nc"]]]
                    , Lock "B" (
                        Unlock (
                          Interaction "B" "A"
                            [ ( Composed EXP [ Atomic "Nc", Composed MULT [Atomic "Na", Atomic "Nb"]]
                              , Lock "A" (
                                  Nonce "MESS" (
                                    Unlock (
                                      Interaction "A" "B"
                                        [ (Composed PAIR [Atomic "MESS", Composed EXP [Atomic "Nc", Composed MULT [Atomic "Nb", Composed MULT [Atomic "Na", Atomic "MESS"]]]], Nil) ]
                                        Epsilon
                                    )
                                  )
                                )
                              )
                            ]
                            Epsilon
                        )
                      )
                    )
                  ]
                  Epsilon
              )
            )
            )
          )
        )
    , protocolGoals = []
    }

protoExp2 :: ProtocolDescription
protoExp2 =
  ProtocolDescription
    { protocolAlgebra = Map.empty
    , protocolCells   = Map.empty
    , protocolSigma0  = Sigma { public = Map.empty, private = Map.empty, relation = Map.empty }
    , protocolSigma   = Sigma { public = Map.empty, private = Map.empty, relation = Map.empty }
    , protocolRoles   = Map.fromList
        [ ( "A"
          , RoleInfo
              { roleKnowledge = []
              , roleChoice    = Nothing
              }
          )
        , ( "B"
          , RoleInfo
              { roleKnowledge = []
              , roleChoice    = Nothing
              }
          )
        ]
    , protocolChoreo  =
        Lock "A" (
          Nonce "Na" (
            Nonce "Nb" (
              Nonce "Nc" (
              Unlock (
                Interaction "A" "B"
                  [ ( Composed PAIR [ Composed PAIR [Atomic "Na", Atomic "Nb"], Composed PAIR [Atomic "Nc", Composed EXP [ Atomic "Nc", Composed MULT [Atomic "Na", Atomic "Nb"] ]]]
                    , Lock "B" (
                        Unlock (
                          Interaction "B" "A"
                            [ ( Atomic "Nc"
                              , Lock "A" (
                                  Nonce "MESS" (
                                    Unlock (
                                      Interaction "A" "B"
                                        [ (Composed PAIR [Atomic "MESS", Composed MULT [Atomic "Na", Atomic "MESS"]], Nil) ]
                                        Epsilon
                                    )
                                  )
                                )
                              )
                            ]
                            Epsilon
                        )
                      )
                    )
                  ]
                  Epsilon
              )
            )
            )
          )
        )
    , protocolGoals = []
    }

tests :: TestTree
tests =
  testGroup
    "Translation with equational theory operators"
    [ 
        unit_dh
      , unit_mult
      , unit_exp
      , unit_exp2
    ]

unit_dh :: TestTree
unit_dh =
  testCase "Variable in frame" $ do
    let sprotocol = translateProtocol protoDH
    case sprotocol of
      Right protocol -> prettySProtocol protocol @?= "theory ChoreoTheory\nbegin\nbuiltins: symmetric-encryption, diffie-hellman\nfunctions: g/0, true/0 [private]\nlet A(A) =\n  new Na;\n  out(exp(g, Na));\n  in(X1);\n  new MESS;\n  out(senc(MESS, exp(exp(g, Nb), Na)));\n  in(X3);\n  if MESS = X3 then\n    0\nlet B(B) =\n  in(X0);\n  new Nb;\n  out(exp(g, Nb));\n  in(X2);\n  let MESS = sdec(X2, exp(X0, Nb)) in\n    out(MESS);\n    0\nprocess: \n  new dishonest;\n  out(dishonest);\n  ! new agent;\n  event Honest(agent);\n  out(agent);\n  ! (\n    A(agent)\n   | \n    B(agent)\n  )\nend\n"
      Left m -> m @?= ""


unit_mult :: TestTree
unit_mult =
  testCase "Mult checks" $ do
    let sprotocol = translateProtocol protoMult
    case sprotocol of
      Right protocol -> prettySProtocol protocol @?= "theory ChoreoTheory\nbegin\nbuiltins: diffie-hellman\nfunctions: pair/2, true/0 [private]\nlet A(A) =\n  new Na;\n  new Nb;\n  new Nc;\n  out(pair(pair(Na, Nb), pair(Nc, mult(mult(Na, Nb), Nc))));\n  in(X3);\n  new MESS;\n  out(pair(MESS, mult(Na, MESS)));\n  0\nlet B(B) =\n  in(X0);\n  let pair(X1, X2) = X0 in\n    let pair(Na, Nb) = X1 in\n      let pair(Nc, X6) = X2 in\n        out(mult(mult(Na, Nb), Nc));\n        in(X7);\n        let pair(MESS, X9) = X7 in\n          if mult(mult(Nb, Nc), X9) = mult(MESS, X6) then\n            0\nprocess: \n  new dishonest;\n  out(dishonest);\n  ! new agent;\n  event Honest(agent);\n  out(agent);\n  ! (\n    A(agent)\n   | \n    B(agent)\n  )\nend\n"
      Left m -> m @?= ""

unit_exp :: TestTree
unit_exp =
  testCase "Exp1 checks" $ do
    let sprotocol = translateProtocol protoExp1
    case sprotocol of
      Right protocol -> prettySProtocol protocol @?= "theory ChoreoTheory\nbegin\nbuiltins: diffie-hellman\nfunctions: pair/2, true/0 [private]\nlet A(A) =\n  new Na;\n  new Nb;\n  new Nc;\n  out(pair(pair(Na, Nb), pair(Nc, mult(mult(Na, Nb), Nc))));\n  in(X3);\n  new MESS;\n  out(pair(MESS, exp(Nc, mult(Nb, mult(Na, MESS)))));\n  0\nlet B(B) =\n  in(X0);\n  let pair(X1, X2) = X0 in\n    let pair(Na, Nb) = X1 in\n      let pair(Nc, X6) = X2 in\n        out(exp(Nc, mult(Na, Nb)));\n        in(X7);\n        let pair(MESS, X9) = X7 in\n          if exp(Nc, mult(X6, MESS)) = exp(X9, Nc) then\n            0\nprocess: \n  new dishonest;\n  out(dishonest);\n  ! new agent;\n  event Honest(agent);\n  out(agent);\n  ! (\n    A(agent)\n   | \n    B(agent)\n  )\nend\n"
      Left m -> m @?= ""

unit_exp2 :: TestTree
unit_exp2 =
  testCase "Exp2 checks" $ do
    let sprotocol = translateProtocol protoExp2
    case sprotocol of
      Right protocol -> prettySProtocol protocol @?= "theory ChoreoTheory\nbegin\nbuiltins: diffie-hellman\nfunctions: pair/2, true/0 [private]\nlet A(A) =\n  new Na;\n  new Nb;\n  new Nc;\n  out(pair(pair(Na, Nb), pair(Nc, exp(Nc, mult(Na, Nb)))));\n  in(X3);\n  if Nc = X3 then\n    new MESS;\n    out(pair(MESS, mult(Na, MESS)));\n    0\nlet B(B) =\n  in(X0);\n  let pair(X1, X2) = X0 in\n    let pair(Na, Nb) = X1 in\n      let pair(Nc, X6) = X2 in\n        out(Nc);\n        in(X7);\n        let pair(MESS, X9) = X7 in\n          if exp(Nc, mult(X9, Nb)) = exp(X6, MESS) then\n            0\nprocess: \n  new dishonest;\n  out(dishonest);\n  ! new agent;\n  event Honest(agent);\n  out(agent);\n  ! (\n    A(agent)\n   | \n    B(agent)\n  )\nend\n"
      Left m -> m @?= ""