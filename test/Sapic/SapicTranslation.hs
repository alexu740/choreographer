{-# LANGUAGE OverloadedStrings #-}

module Sapic.SapicTranslation where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import Data.Traversable (mapAccumL)

import qualified Data.Set as Set

import Compiler.ToSapicPlus.Translation
  ( translateChoreographyToSapicProcess
  , createInitialFrameChoreographyPair,
  translateAgent,
  translateProtocol,
  translateProcessBody
  )
import Compiler.ToSapicPlus.PrettyPrinter
import Compiler.ToSapicPlus.TranslationCases.Receive

import qualified Types.Rewrite as RW

import Compiler.ToSapicPlus.RewriteSystem.TermRewriter
import Compiler.ToSapicPlus.CheckGenerator

import Compiler.ToSapicPlus.RewriteSystem.Rule (rules, toSRule)
import Compiler.ToSapicPlus.RewriteSystem.RewriteReceipt (RewriteReceipt(..))
import Compiler.ToSapicPlus.RewriteSystem.RewriteSystem

import Compiler.ToSapicPlus.SFrame (SFrame(..), emptyFrame, insertTermsInFrame)
import Compiler.ToSapicPlus.SyntacticSimplifier(compressIfBlocksOnSingularSyntacticBranch)
import Compiler.ToSapicPlus.InitialKnowledgeDistributor
import Compiler.ToSapicPlus.RecipeUtility
  ( constructCommmonRecipe )

import Types.Choreography
  ( Choreography(..)
  , Term(..)
  , Atomic(..)
  , Agent
  , CDefault(..)
  )
import Types.Sapic
  ( SProcess(..)
  , SVariable
  , SRecipe(..)
  , STerm(..)
  , SPattern(..)
  , SPatternArg(..), SProtocol (SProtocol, agentProcesses, protocolHeader, mainProcess)
  , Rule(..), RTerm(..)
  )
import Types.Simple (FUNCTIONS(..))
import Types.ChoreographyProtocolShell
  ( ProtocolDescription(..)
  , RoleInfo(..)
  , Sigma(..)
  , SecurityGoal(..)
  )
import qualified Control.Applicative as List


main :: IO ()
main = defaultMain tests

--------------------------------------------------------------------------------
-- Test tree
--------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Compiler.ToSapicPlus.Translation"
  [ 
   unit_createInitialFrame_known_agent_populates_frame,
   unit_createInitialFrame_unknown_agent_errors,
   unit_translate_minimal_protocol_returns_SNil,
   unit_translate_simple,
   unit_translate_send,
   unit_build_recipe,
   unit_translate_receive,
   unit_rewrite_phase1,
   unit_rewrite_deconstruction,
   unit_phase2,
   unit_translation_conditional,
   unit_translation_write,
   unit_translation_read,
   unit_translation_nspk_simple,
   unit_classification,
   unit_printing, 
   unit_rules,
   unit_goals
  ]

protoMinimal :: ProtocolDescription
protoMinimal =
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
    , protocolChoreo = Nil
    , protocolGoals = List.empty
    }

protoSimple :: ProtocolDescription
protoSimple =
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
    , protocolChoreo = Lock "A" (Nonce "Na" (Unlock Nil))
    , protocolGoals = List.empty
    }

unit_createInitialFrame_known_agent_populates_frame :: TestTree
unit_createInitialFrame_known_agent_populates_frame =
  testCase "Initial knowledge enrichment" $ do
    let agent = "A" :: Agent
    let res = createInitialFrameChoreographyPair protoMinimal agent
    case res of
      Left err ->
        assertFailure $ "unexpected Left: " <> T.unpack err
      Right (SFrame mp _ _ _ _ _, chor) -> do
        chor @?= Nil
        Map.size mp @?= 2
        Map.lookup ("X0" :: SVariable) mp @?= Just (Atomic "hello")
        Map.lookup ("X1" :: SVariable) mp @?= Just (Composed PAIR [Atomic "x", Atomic "y"])

unit_createInitialFrame_unknown_agent_errors :: TestTree
unit_createInitialFrame_unknown_agent_errors =
  testCase "Reject unknown agent" $ do
    let agent = "Z" :: Agent
    let res = createInitialFrameChoreographyPair protoMinimal agent
    case res of
      Left err  -> err @?= "Unknown agent: \"Z\""
      Right _   -> assertFailure "expected Left for unknown agent"

unit_translate_minimal_protocol_returns_SNil :: TestTree
unit_translate_minimal_protocol_returns_SNil =
  testCase "Translation of nil process" $ do
    let agent = "A" :: Agent
    let res = translateChoreographyToSapicProcess protoMinimal agent
    res @?= Right SNil

unit_translate_simple :: TestTree
unit_translate_simple =
  testCase "Translation of nonce operation" $ do
    let agentA = "A" :: Agent
    let translationForA = translateChoreographyToSapicProcess protoSimple agentA

    let agentB = "B" :: Agent
    let translationForB = translateChoreographyToSapicProcess protoSimple agentB

    translationForA @?= Right (SNew (TName "Na") SNil)
    translationForB @?= Right SNil

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

unit_translate_send :: TestTree
unit_translate_send =
  testCase "Translation of send operation" $ do
    let agentA = "A" :: Agent
    let translationForA = translateChoreographyToSapicProcess protoInteractionSimple agentA
    translationForA @?= Right (SOut [(TName "hello",SNil)])

unit_build_recipe :: TestTree
unit_build_recipe =
  testCase "Composition of terms" $ do
    let frame = SFrame {
      mapping = Map.fromList [
        ("X1", Atomic "Na")
      ]
      ,receipts = List.empty
      ,deconstructed = List.empty
      ,prevChecks = List.empty
      ,bounded = List.empty
      ,initial =  List.empty
    }

    let branchTerm = Composed PAIR [Atomic "Na", Atomic "Na"]
    let uncomposableTermDueToKnowledge = Composed PAIR [Atomic "Na", Atomic "Nb"]
    let uncomposableTermDueToConstructor = Composed INV [Atomic "Na"]

    let recipe1 = constructCommmonRecipe protoInteractionReceiveWithIfs [(frame, branchTerm)]
    let recipe2 = constructCommmonRecipe protoInteractionReceiveWithIfs [(frame, uncomposableTermDueToKnowledge)]
    let recipe3 = constructCommmonRecipe protoInteractionReceiveWithIfs [(frame, uncomposableTermDueToConstructor)]

    recipe1 @?= Right (RFunction PAIR [RVariable "X1",RVariable "X1"])
    recipe2 @?= Left "NoCommonRecipe: [(fromList [(\"X1\",Atomic \"Na\")],Composed PAIR [Atomic \"Na\",Atomic \"Nb\"])]"
    recipe3 @?= Left "NoCommonRecipe: [(fromList [(\"X1\",Atomic \"Na\")],Composed INV [Atomic \"Na\"])]"

unit_translate_receive :: TestTree
unit_translate_receive =
  testCase "Translation of receive operation" $ do
    let agentB = "B" :: Agent

    let frame = SFrame {
      mapping = Map.fromList [
        ("X0", Atomic "Na")
      ]
      ,receipts = List.empty
      ,deconstructed = List.empty
      ,prevChecks = List.empty
      ,bounded = List.empty
      ,initial =  List.empty
    }

    let translationForB = translateChoreographyToSapicProcess protoInteractionSimple agentB
    let translationForBWithDestr = translateChoreographyToSapicProcess protoInteractionReceiveWithIfs agentB
    translationForB @?= Right (SIn (TName "hello") SNil)

    case translationForBWithDestr of
      Right tr -> do
        let squashed = compressIfBlocksOnSingularSyntacticBranch tr
        squashed @?= SIn (TVariable "X2") (SLet (PTerm (TVariable "X3")) (TFunction DSCRYPT [TName "x",TVariable "X2"]) (SLet (PData PAIR [PBind (TName "y"),PCompare (TName "q")]) (TVariable "X3") SNil SNil) SNil)

protoInteractionReceiveWithIfs:: ProtocolDescription
protoInteractionReceiveWithIfs =
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
        [ ("A", RoleInfo { roleKnowledge = [ Atomic "hello", Composed PAIR [Atomic "x", Atomic "y"]], roleChoice = Nothing})
        , ("B", RoleInfo { roleKnowledge = [Atomic "x", Atomic "q"], roleChoice = Nothing })]
    , protocolChoreo = Interaction "A" "B" [(Composed SCRYPT [Atomic "x", Composed PAIR [Atomic "y", Atomic "q"], Atomic "r"], Nil)] Epsilon
    , protocolGoals = List.empty
    }

protoInteractionComplex :: ProtocolDescription
protoInteractionComplex =
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
        [ ("A", RoleInfo { roleKnowledge = [ Atomic "hello", Composed PAIR [Atomic "x", Atomic "y"]], roleChoice = Nothing})
        , ("B", RoleInfo { roleKnowledge = [Atomic "x"], roleChoice = Nothing })
        ]
    , protocolChoreo = Interaction "A" "B" [(Composed SCRYPT [Atomic "x", Composed PAIR [Atomic "y", Atomic "q"], Atomic "r"], Nil)] Epsilon
    , protocolGoals = List.empty
    }

unit_rewrite_phase1 :: TestTree
unit_rewrite_phase1 =
  testCase "Rewrite rule application" $ do
    let agentB = "B" :: Agent

    let frame = SFrame {
      mapping = Map.fromList [
        ("X0", Atomic "Na"),
        ("X1", Composed PAIR [Atomic "Na", Atomic "Nb"]),
        ("X2", Composed SENC [Atomic "MESSAGE", Atomic "Nb"])
      ]
      ,receipts = List.empty
      ,deconstructed = List.empty
      ,prevChecks = List.empty
      ,bounded = List.empty
      ,initial =  List.empty
    }
    let rs = getRewriteSystem protoInteractionComplex
    let decomposableTerms = findTermsThatCanBeDeconstructed frame
    let discoveredTerms = [(result, rule, term) | term <- decomposableTerms , rule <- rules , Just result <- [applyRule rs frame rule term]]

    let (frame', receipts) = analyzePhase1States protoInteractionComplex [frame]
    let translationForB = translateChoreographyToSapicProcess protoInteractionComplex agentB
    translationForB @?= Right (SIn (TVariable "X1") (SLet (PTerm (TVariable "X2")) (TFunction DSCRYPT [TName "x",TVariable "X1"]) (SLet (PData PAIR [PBind (TName "y"),PBind (TName "q")]) (TVariable "X2") SNil SNil) SNil))
    receipts @?= [
      RewriteReceipt {frameKey = "X3", subject = Composed PAIR [Atomic "Na",Atomic "Nb"], rule = Rule { destructor = PROJ1, args = [RConstr PAIR [RVar "PAIR1",RVar "PAIR2"]], result = RVar "PAIR1"}, subjectRecipe = "X1", ruleFunction = PROJ1, ruleArgsToTermsMap = [], ruleArgsToRecipeMap = []},
      RewriteReceipt {frameKey = "X4", subject = Composed PAIR [Atomic "Na",Atomic "Nb"], rule = Rule { destructor = PROJ2, args = [RConstr PAIR [RVar "PAIR1",RVar "PAIR2"]], result = RVar "PAIR2"}, subjectRecipe = "X1", ruleFunction = PROJ2, ruleArgsToTermsMap = [], ruleArgsToRecipeMap = []},
      RewriteReceipt {frameKey = "X5", subject = Composed SENC [Atomic "MESSAGE",Atomic "Nb"], rule = Rule {destructor = SDEC, args = [RConstr SENC [RVar "MSG",RVar "KEY"],RVar "KEY"], result = RVar "MSG"}, subjectRecipe = "X2", ruleFunction = SDEC, ruleArgsToTermsMap = [(RVar "KEY",Atomic "Nb")], ruleArgsToRecipeMap = [(RVar "KEY",TVariable "X4")]}]
    frame' @?= [SFrame {
      mapping = Map.fromList [("X0",Atomic "Na"),("X1",Composed PAIR [Atomic "Na",Atomic "Nb"]),("X2", Composed SENC [Atomic "MESSAGE", Atomic "Nb"]),("X3",Atomic "Na"),("X4",Atomic "Nb"),("X5",Atomic "MESSAGE")], 
      deconstructed = ["X2","X1","X1"], 
      receipts = [
        RewriteReceipt {frameKey = "X5", subject = Composed SENC [Atomic "MESSAGE",Atomic "Nb"], rule = Rule {destructor = SDEC, args = [RConstr SENC [RVar "MSG",RVar "KEY"],RVar "KEY"], result = RVar "MSG"}, subjectRecipe = "X2", ruleFunction = SDEC, ruleArgsToTermsMap = [(RVar "KEY",Atomic "Nb")], ruleArgsToRecipeMap = [(RVar "KEY",TVariable "X4")]},
        RewriteReceipt {frameKey = "X4", subject = Composed PAIR [Atomic "Na",Atomic "Nb"], rule = Rule { destructor = PROJ2, args = [RConstr PAIR [RVar "PAIR1",RVar "PAIR2"]], result = RVar "PAIR2"}, subjectRecipe = "X1", ruleFunction = PROJ2, ruleArgsToTermsMap = [], ruleArgsToRecipeMap = []},
        RewriteReceipt {frameKey = "X3", subject = Composed PAIR [Atomic "Na",Atomic "Nb"], rule = Rule { destructor = PROJ1, args = [RConstr PAIR [RVar "PAIR1",RVar "PAIR2"]], result = RVar "PAIR1"}, subjectRecipe = "X1", ruleFunction = PROJ1, ruleArgsToTermsMap = [], ruleArgsToRecipeMap = []}], 
      prevChecks = [],
      bounded = ["X5", "X4"],
      initial = []
      }]

unit_rewrite_deconstruction :: TestTree
unit_rewrite_deconstruction =
  testCase "Analysis phase 1" $ do
    let frame = SFrame {
      mapping = Map.fromList [
        ("X0", Atomic "Na"),
        ("X1", Composed PAIR [Atomic "Na", Atomic "Nb"]),
        ("X2", Composed AENC [Atomic "MESSAGE", Atomic "Nb"])
      ]
      , deconstructed = List.empty
      , receipts = List.empty
      , prevChecks = List.empty
      , bounded = List.empty
      , initial =  List.empty
    }

    let rule = Rule {
      destructor = ADEC
      , args =
          [ 
            RConstr AENC [ RVar "MSG", RConstr PK [RVar "KEY"] ],
            RVar "KEY"
          ]
      , result = RVar "MSG"
    }

    let term = Composed AENC [Atomic "MESSAGE", Composed PK [Atomic "Na"]]
    let previousReceipts = []

    let rs = getRewriteSystem protoInteractionComplex
    let alreadyDone = alreadyDecomposed rule term previousReceipts
    let matchesRule = isMatchRuleShape rule term
    let res = applyRule rs frame rule term
    alreadyDone @?= False
    matchesRule @?= True
    res @?= Just (Atomic "MESSAGE",[(RVar "KEY",Atomic "Na")])

unit_phase2 :: TestTree
unit_phase2 =
  testCase "Analysis phase 2" $ do
    let frame0 = SFrame {
      mapping = Map.fromList [
        ("X0", Atomic "Na"),
        ("X1", Composed PAIR [Atomic "Na", Atomic "Nb"]),
        ("X2", Composed CRYPT [Atomic "Nb", Atomic "MESSAGE"])
      ]
      , deconstructed = List.empty
      , receipts = List.empty
      , prevChecks = List.empty
      , bounded = List.empty
      , initial = List.empty
    }

    let frame1 = SFrame {
      mapping = Map.fromList [
        ("X0", Atomic "Na"),
        ("X1", Composed PAIR [Atomic "Na", Atomic "Nb"]),
        ("X2", Composed CRYPT [Atomic "Nb", Atomic "MESSAGE"]),
        ("X3", Atomic "Na")
      ]
      , deconstructed = List.empty
      , receipts = List.empty
      , prevChecks = List.empty
      , bounded = List.empty
      , initial = List.empty
    }

    let frame = SFrame {
      mapping = Map.fromList [
        ("X0", Atomic "Na"),
        ("X1", Composed PAIR [Atomic "Na", Atomic "Nb"]),
        ("X2", Composed CRYPT [Atomic "Nb", Atomic "MESSAGE"]),
        ("X3", Composed INV [Atomic "Na"]),
        ("X4", Composed PAIR [Atomic "Na", Atomic "Nb"])
      ]
      , deconstructed = List.empty
      , receipts = List.empty
      , prevChecks = []
      , bounded = List.empty
      , initial = List.empty
    }

    let frame2 = SFrame {
      mapping = Map.fromList [
        ("X0", Atomic "Na"),
        ("X1", Composed PAIR [Atomic "Na", Atomic "Nb"]),
        ("X2", Composed CRYPT [Atomic "Nb", Atomic "MESSAGE"]),
        ("X3", Composed INV [Atomic "Na"]),
        ("X4", Composed PAIR [Atomic "Na", Atomic "Nb"])
      ]
      , deconstructed = List.empty
      , receipts = List.empty
      , prevChecks = [
        (RVariable "X1",RVariable "X4"),
        (RFunction VCRYPT [RVariable "X3", RFunction CRYPT [RVariable "X0",RVariable "__TRUE__"]], RVariable "__TRUE__"),
        (RVariable "X1",RVariable "X4")
      ]
      , bounded = List.empty
      , initial = List.empty
    }

    let frame3 = SFrame {
      mapping = Map.fromList [
        ("X0", Atomic "Na"),
        ("X1", Composed PAIR [Atomic "Na", Atomic "Nb"]),
        ("X2", Composed CRYPT [Atomic "Nb", Atomic "MESSAGE"])
      ]
      , deconstructed = List.empty
      , receipts = List.empty
      , prevChecks = List.empty
      , bounded = List.empty
      , initial = List.empty
    }

    let res0 = analyzePhase2States protoInteractionReceiveWithIfs [frame0]
    let res1 = analyzePhase2States protoInteractionReceiveWithIfs [frame1]
    let res2 = analyzePhase2States protoInteractionReceiveWithIfs [frame]
    let res3 = analyzePhase2States protoInteractionReceiveWithIfs [frame2]

    res0 @?= ([SFrame {mapping = Map.fromList [("X0",Atomic "Na"),("X1",Composed PAIR [Atomic "Na",Atomic "Nb"]),("X2",Composed CRYPT [Atomic "Nb",Atomic "MESSAGE"])], initial = List.empty, deconstructed = [], receipts = [], prevChecks = [], bounded = List.empty}],[])
    res1 @?= ([SFrame {mapping = Map.fromList [("X0",Atomic "Na"),("X1",Composed PAIR [Atomic "Na",Atomic "Nb"]),("X2",Composed CRYPT [Atomic "Nb",Atomic "MESSAGE"]),("X3",Atomic "Na")], initial = List.empty, deconstructed = [], receipts = [], prevChecks = [(RVariable "X0",RVariable "X3"),(RVariable "X0",RVariable "X3")], bounded = List.empty}],[(RVariable "X0",RVariable "X3")])
    res2 @?= ([SFrame {mapping = Map.fromList [("X0",Atomic "Na"),("X1",Composed PAIR [Atomic "Na",Atomic "Nb"]),("X2",Composed CRYPT [Atomic "Nb",Atomic "MESSAGE"]),("X3",Composed INV [Atomic "Na"]),("X4",Composed PAIR [Atomic "Na",Atomic "Nb"])], initial = List.empty, deconstructed = [], bounded = [], receipts = [], prevChecks = [(RVariable "X1",RVariable "X4"),(RVariable "X1",RVariable "X4")]}],[(RVariable "X1",RVariable "X4")])
    res3 @?= ([SFrame {mapping = Map.fromList [("X0",Atomic "Na"),("X1",Composed PAIR [Atomic "Na",Atomic "Nb"]),("X2",Composed CRYPT [Atomic "Nb",Atomic "MESSAGE"]),("X3",Composed INV [Atomic "Na"]),("X4",Composed PAIR [Atomic "Na",Atomic "Nb"])], initial = List.empty, deconstructed = [], receipts = [], prevChecks = [(RVariable "X1",RVariable "X4"),(RFunction VCRYPT [RVariable "X3",RFunction CRYPT [RVariable "X0",RVariable "__TRUE__"]],RVariable "__TRUE__"),(RVariable "X1",RVariable "X4")]      , bounded = List.empty}],[])

unit_translation_conditional :: TestTree
unit_translation_conditional =
  testCase "Translation of conditional (if)" $ do
    let agentA = "A" :: Agent
    let proto = ProtocolDescription
          { protocolAlgebra = Map.empty,
            protocolCells =  Map.empty,
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
              [ ("A", RoleInfo {  roleKnowledge = [ Atomic "x", Atomic "y"], roleChoice = Nothing})
              , ("B", RoleInfo { roleKnowledge = [Atomic "x"], roleChoice = Nothing })
              ]
          , protocolChoreo = Lock "A" (
                              If (Atomic "x") (Atomic "y") 
                              (Nonce "Na" (
                                  Unlock Nil
                                )
                              ) 
                              (Nonce "Nb" (
                                Unlock Nil
                                )
                              )
                            )
          , protocolGoals = List.empty
          }
    
    let translationForA = translateChoreographyToSapicProcess proto agentA
    translationForA @?= Right (SIf (TVariable "X0") (TVariable "X1") (SNew (TName "Na") SNil) (SNew (TName "Nb") SNil))

unit_translation_write :: TestTree
unit_translation_write =
  testCase "Write to cell" $ do
    let agentA = "A" :: Agent
    let proto = ProtocolDescription
          { protocolAlgebra = Map.empty,
            protocolCells =  Map.empty,
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
              [ ("A", RoleInfo { roleKnowledge = [ Atomic "cellA", Atomic "key", Atomic "value" ], roleChoice = Nothing })
              , ("B", RoleInfo { roleKnowledge = [], roleChoice = Nothing })
              ]
          , protocolChoreo =
              Lock "A" (
                Write "cellA" (Atomic "key") (Atomic "value") (
                  Unlock Nil
                )
              )
          , protocolGoals = List.empty
          }
    let translationForA = translateChoreographyToSapicProcess proto agentA
    translationForA @?= Right (SInsert (TFunction CELL [TVariable "X0",TVariable "X1"]) (TVariable "X2") SNil)

unit_translation_read :: TestTree
unit_translation_read =
  testCase "Read from cell" $ do
    let agentA = "A" :: Agent
    let proto = ProtocolDescription
          { protocolAlgebra = Map.empty,
            protocolCells =  Map.empty,
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
              [ ("A", RoleInfo { roleKnowledge = [Atomic "cellA", Atomic "key"], roleChoice = Nothing })
              , ("B", RoleInfo { roleKnowledge = [], roleChoice = Nothing })
              ]
          , protocolChoreo =
              Lock "A" (
                Read "x" "cellA" (Atomic "key") (
                  Unlock Nil
                )
              )
          , protocolGoals = List.empty
          }
    let translationForA = translateChoreographyToSapicProcess proto agentA
    translationForA @?= Right (SLookup (TFunction CELL [TVariable "X0",TVariable "X1"]) "X2" SNil SNil)

unit_translation_nspk_simple :: TestTree
unit_translation_nspk_simple =
  testCase "Simple NSPK translation for roles A and B" $ do
    let agentA = "A" :: Agent
    let agentB = "B" :: Agent
    let proto = ProtocolDescription
          {       
            protocolSigma = Sigma {
              public = Map.empty,
              private = Map.empty,
              relation = Map.empty
            },
            protocolSigma0 = Sigma {
              public = Map.empty,
              private = Map.empty,
              relation = Map.empty
            },
            protocolAlgebra = Map.empty,
            protocolCells = Map.empty,
            protocolRoles  = Map.fromList
              [ ("A", RoleInfo { roleKnowledge = [Atomic "A", Atomic "B", Composed INV [Atomic "A"], Composed PK [Composed INV [Atomic "A"]], Composed PK [Composed INV [Atomic "B"]]], roleChoice = Nothing })
              , ("B", RoleInfo { roleKnowledge = [Atomic "B", Atomic "A", Composed INV [Atomic "B"], Composed PK [Composed INV [Atomic "B"]], Composed PK [Composed INV [Atomic "A"]]], roleChoice = Nothing })
              ]
          , protocolChoreo =
              Lock "A" (
                Nonce "Na" (
                    Unlock (
                      Interaction "A" "B" [(Composed AENC [Composed PAIR [Atomic "A", Atomic "Na"], Composed PK [Composed INV [Atomic "B"]]], 
                        Lock "B" (
                          Nonce "Nb" (
                            Unlock (
                              Interaction "B" "A" [(
                                Composed AENC [Composed PAIR [Atomic "Na", Atomic "Nb"], Composed PK [Composed INV [Atomic "A"]]],
                                Interaction "A" "B" [(
                                  Composed AENC [Atomic "Nb", Composed PK [Composed INV [Atomic "B"]]], 
                                  Nil
                                )] Epsilon
                              )] 
                              Epsilon
                            )
                          )
                        )
                      )] 
                      Epsilon
                  )
                )
              )
            , protocolGoals = List.empty
          }

    let translationForA = translateChoreographyToSapicProcess proto agentA
    let translationForB = translateChoreographyToSapicProcess proto agentB
    case translationForA of
      Right tr -> do
        let squashed = compressIfBlocksOnSingularSyntacticBranch tr
        squashed @?= SNew (TName "Na") (SOut [(TFunction AENC [TFunction PAIR [TName "A",TName "Na"],TFunction PK [TFunction INV [TName "B"]]],SIn (TVariable "X6") (SLet (PTerm (TVariable "X7")) (TFunction ADEC [TVariable "X6",TFunction INV [TName "A"]]) (SLet (PData PAIR [PCompare (TName "Na"),PBind (TName "Nb")]) (TVariable "X7") (SOut [(TFunction AENC [TName "Nb",TFunction PK [TFunction INV [TName "B"]]],SNil)]) SNil) SNil))])
      Left er ->
        er @?= "Error"

    case translationForB of
      Right tr -> do
        let squashed = compressIfBlocksOnSingularSyntacticBranch tr
        squashed @?= SIn (TVariable "X5") (SLet (PTerm (TVariable "X6")) (TFunction ADEC [TVariable "X5",TFunction INV [TName "B"]]) (SLet (PData PAIR [PCompare (TName "A"),PBind (TName "Na")]) (TVariable "X6") (SNew (TName "Nb") (SOut [(TFunction AENC [TFunction PAIR [TName "Na",TName "Nb"],TFunction PK [TFunction INV [TName "A"]]],SIn (TVariable "X10") (SLet (PTerm (TVariable "X11")) (TFunction ADEC [TVariable "X10",TFunction INV [TName "B"]]) (SIf (TVariable "X11") (TName "Nb") SNil SNil) SNil))])) SNil) SNil)
      Left er ->
        er @?= "Error"

unit_classification :: TestTree
unit_classification =
  testCase "Raw translation of a role and derivation of dependent roles" $ do
    let choreo = ProtocolDescription
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
              [ ("A", RoleInfo { roleKnowledge = [Atomic "A", Atomic "B", Composed INV [Atomic "A"], Composed PK [Composed INV [Atomic "A"]], Composed PK [Composed INV [Atomic "B"]]], roleChoice = Nothing })
              , ("B", RoleInfo { roleKnowledge = [Atomic "A", Atomic "B", Composed INV [Atomic "B"], Composed PK [Composed INV [Atomic "B"]], Composed PK [Composed INV [Atomic "A"]]], roleChoice = Nothing })
              ]
          , protocolChoreo =
              Lock "A" (
                Nonce "Na" (
                    Unlock (
                      Interaction "A" "B" [(Composed AENC [Composed PAIR [Atomic "A", Atomic "Na"], Composed PK [Composed INV [Atomic "B"]]], 
                        Lock "B" (
                          Nonce "Nb" (
                            Unlock (
                              Interaction "B" "A" [(
                                Composed AENC [Composed PAIR [Atomic "Na", Atomic "Nb"], Composed PK [Composed INV [Atomic "A"]]],
                                Interaction "A" "B" [(
                                  Composed AENC [Atomic "Nb", Composed PK [Composed INV [Atomic "B"]]], 
                                  Nil
                                )] Epsilon
                              )] Epsilon
                            )
                          )
                        )
                    )] Epsilon
                    )
                  )
                )
            , protocolGoals = List.empty
          }
    let roleK = [Atomic "A", Atomic "B", Composed INV [Atomic "A"]]
    let dependant = getDependantRolesFromKnowledge "A" roleK choreo
    
    let translationForA = translateProcessBody choreo "A"
    case translationForA of
      Right tr -> tr @?= SIn (TVariable "B") (SNew (TName "Na") (SOut [(TFunction AENC [TFunction PAIR [TName "A",TName "Na"],TFunction PK [TFunction INV [TName "B"]]],SIn (TVariable "X6") (SLet (PTerm (TVariable "X7")) (TFunction ADEC [TVariable "X6",TFunction INV [TName "A"]]) (SLet (PData PAIR [PCompare (TName "Na"),PBind (TName "Nb")]) (TVariable "X7") (SOut [(TFunction AENC [TName "Nb",TFunction PK [TFunction INV [TName "B"]]],SNil)]) SNil) SNil))]))
      Left m -> m @?= ""

    case dependant of
      Right r -> r @?= ["B"]
      Left m -> m @?= ""

unit_printing :: TestTree
unit_printing =
  testCase "Pretty print of final protocol" $ do
    let choreo = ProtocolDescription
          { 
          protocolSigma0 = Sigma {
            public = Map.empty,
            private = Map.empty,
            relation = Map.empty
          },
          protocolCells = Map.empty,
          protocolAlgebra = Map.fromList [
            ( UnDef "D", (
                [ RW.RewriteVar RW.KEY
                , RW.Comp (UnDef "C")
                    [ RW.Comp INV [  RW.RewriteVar RW.KEY ]
                    , RW.RewriteVar RW.MSG
                    ]
                ], RW.RewriteVar RW.MSG
          ))],
          protocolSigma = Sigma {
            public = Map.empty,
            private = Map.empty,
            relation = Map.empty
          },
          protocolRoles  = Map.fromList
            [ ("A", RoleInfo { roleKnowledge = [Atomic "A", Atomic "B", Composed PRIV [Atomic "A"], Composed PK [Composed PRIV [Atomic "A"]], Composed PK [Composed PRIV [Atomic "B"]]], roleChoice = Nothing })
            , ("B", RoleInfo { roleKnowledge = [Atomic "A", Atomic "B", Composed PRIV [Atomic "B"], Composed PK [Composed PRIV [Atomic "B"]], Composed PK [Composed PRIV [Atomic "A"]]], roleChoice = Nothing })
            ]
          , 
          protocolChoreo =
              Lock "A" (
                Nonce "Na" (
                    Unlock (
                      Interaction "A" "B" [(Composed AENC [Composed PAIR [Composed REVEALSIGN [Atomic "A", Composed PRIV [Atomic "A"]], Composed H [Atomic "Na"]], Composed PK [Composed PRIV [Atomic "B"]]], 
                        Lock "B" (
                          Nonce "Nb" (
                            Unlock (
                              Interaction "B" "A" [(
                                Composed AENC [Composed PAIR [Composed H [Atomic "Na"], Composed PAIR [Atomic "Nb", Atomic "B"]], Composed PK [Composed PRIV [Atomic "A"]]],
                                Interaction "A" "B" [(
                                  Composed AENC [Composed H [Atomic "Na"], Composed PK [Composed PRIV [Atomic "B"]]], 
                                  Nil
                                )] Epsilon
                              )] Epsilon
                            )
                          )
                        )
                    )] Epsilon
                    )
                  )
              )
          , protocolGoals = List.empty
            }

    let sprotocol = translateProtocol choreo
    case sprotocol of
      Right protocol -> prettySProtocol protocol @?= "theory ChoreoTheory\nbegin\nbuiltins: hashing, asymmetric-encryption, revealing-signing\nfunctions: pair/2, true/0 [private], priv/1 [private]\nequations:\n  d(key, c(inv(key), msg)) = msg\nlet A(A) =\n  in(B);\n  new Na;\n  out(aenc(pair(revealsign(A, priv(A)), h(Na)), pk(priv(B))));\n  in(X6);\n  let X7 = adec(X6, priv(A)) in\n    let pair(=h(Na), X9) = X7 in\n      let pair(Nb, =B) = X9 in\n        out(aenc(h(Na), pk(priv(B))));\n        0\nlet B(B) =\n  in(A);\n  in(X5);\n  let X6 = adec(X5, priv(B)) in\n    let pair(X7, X8) = X6 in\n      let X9 = getmessage(X7) in\n        if revealverify(X7, A, pk(priv(A))) = true then\n          if A = X9 then\n            new Nb;\n            out(aenc(pair(h(Na), pair(Nb, B)), pk(priv(A))));\n            in(X11);\n            let X12 = adec(X11, priv(B)) in\n              if X12 = X8 then\n                0\nprocess: \n  new dishonest;\n  out(dishonest);\n  out(priv(dishonest));\n  ! new agent;\n  event Honest(agent);\n  out(agent);\n  out(pk(priv(agent)));\n  ! (\n    A(agent)\n   | \n    B(agent)\n  )\nend\n"
      Left m -> m @?= ""

unit_rules :: TestTree
unit_rules =
  testCase "Coversion of rule definitions from lexer to sapic format" $ do
    let r = ( DSCRYPT,([ RW.RewriteVar (RW.UnDef "KEY"), RW.Comp SCRYPT [RW.RewriteVar (RW.UnDef "KEY"), RW.RewriteVar (RW.UnDef "MSG"),RW.RewriteVar (RW.UnDef "RANDOM")]], RW.RewriteVar (RW.UnDef "MSG")))
    let r2 = (PROJ1,([ RW.Comp PAIR [ RW.RewriteVar RW.PAIR1, RW.RewriteVar RW.PAIR2]], RW.RewriteVar RW.PAIR1))  
    let m = toSRule r
    let m2 = toSRule r2
    m @?= Rule {destructor = DSCRYPT, args = [RVar "KEY",RConstr SCRYPT [ RVar "KEY", RVar "MSG", RVar "RANDOM"]], result = RVar "MSG"}
    m2 @?= Rule {destructor = PROJ1, args = [RConstr PAIR [RVar "PAIR1",RVar "PAIR2"]], result = RVar "PAIR1"}

unit_goals :: TestTree
unit_goals =
  testCase "Goals are translated into events" $ do
    let choreo = ProtocolDescription
          { 
          protocolSigma0 = Sigma {
            public = Map.empty,
            private = Map.empty,
            relation = Map.empty
          },
          protocolCells = Map.empty,
          protocolAlgebra = Map.fromList [
            ( UnDef "D", (
                [ RW.RewriteVar RW.KEY
                , RW.Comp (UnDef "C")
                    [ RW.Comp INV [  RW.RewriteVar RW.KEY ]
                    , RW.RewriteVar RW.MSG
                    ]
                ], RW.RewriteVar RW.MSG
          ))],
          protocolSigma = Sigma {
            public = Map.empty,
            private = Map.empty,
            relation = Map.empty
          },
          protocolRoles  = Map.fromList
            [ ("A", RoleInfo { roleKnowledge = [Atomic "A", Atomic "B", Composed INV [Atomic "A"], Composed PK [Composed INV [Atomic "A"]], Composed PK [Composed INV [Atomic "B"]]], roleChoice = Nothing })
            , ("B", RoleInfo { roleKnowledge = [Atomic "A", Atomic "B", Composed INV [Atomic "B"], Composed PK [Composed INV [Atomic "B"]], Composed PK [Composed INV [Atomic "A"]]], roleChoice = Nothing })
            ]
          , 
          protocolChoreo =
              Lock "A" (
                Nonce "Na" (
                    Unlock (
                      Interaction "A" "B" [(Composed AENC [Composed PAIR [Composed REVEALSIGN [Atomic "A", Composed INV [Atomic "A"]], Atomic "Na"], Composed PK [Composed INV [Atomic "B"]]], 
                        Lock "B" (
                          Nonce "Nb" (
                            Unlock (
                              Interaction "B" "A" [(
                                Composed AENC [Composed PAIR [Composed H [Atomic "Na"], Composed PAIR [Atomic "Nb", Atomic "B"]], Composed PK [Composed INV [Atomic "A"]]],
                                Interaction "A" "B" [(
                                  Composed AENC [Composed H [Atomic "Na"], Composed PK [Composed INV [Atomic "B"]]], 
                                  Nil
                                )] Epsilon
                              )] Epsilon
                            )
                          )
                        )
                    )] Epsilon
                    )
                  )
              )
          ,
          protocolGoals = [
            Secrecy (Atomic "Na") ["A", "B"],
            Secrecy (Atomic "Nb") ["A", "B"],
            WeakAuth "A" "B" (Atomic "Nb"),
            WeakAuth "B" "A" (Atomic "Na"),
            StrongAuth "A" "B" (Atomic "Nb"),
            StrongAuth "B" "A" (Atomic "Na")
          ]
        }

    let sprotocol = translateProtocol choreo
    case sprotocol of
      Right protocol -> prettySProtocol protocol @?= "theory ChoreoTheory\nbegin\nbuiltins: hashing, asymmetric-encryption, revealing-signing\nfunctions: pair/2, true/0 [private]\nequations:\n  d(key, c(inv(key), msg)) = msg\nlet A(A) =\n  in(B);\n  new Na;\n  event Witness(A, B, 'WeakAuthBAAtomicNa', Na);\n  event Witness(A, B, 'StrongAuthBAAtomicNa', Na);\n  out(aenc(pair(revealsign(A, inv(A)), Na), pk(inv(B))));\n  in(X6);\n  let X7 = adec(X6, inv(A)) in\n    let pair(=h(Na), X9) = X7 in\n      let pair(Nb, =B) = X9 in\n        out(aenc(h(Na), pk(inv(B))));\n        new sid;\n        event Request(A, B, 'WeakAuthABAtomicNb', Nb, sid);\n        event Request(A, B, 'StrongAuthABAtomicNb', Nb, sid);\n        event Secret(Na, A, B);\n        event Secret(Nb, A, B);\n        0\nlet B(B) =\n  in(A);\n  in(X5);\n  let X6 = adec(X5, inv(B)) in\n    let pair(X7, Na) = X6 in\n      let X9 = getmessage(X7) in\n        if revealverify(X7, A, pk(inv(A))) = true then\n          if A = X9 then\n            new Nb;\n            event Witness(B, A, 'WeakAuthABAtomicNb', Nb);\n            event Witness(B, A, 'StrongAuthABAtomicNb', Nb);\n            out(aenc(pair(h(Na), pair(Nb, B)), pk(inv(A))));\n            in(X11);\n            let X12 = adec(X11, inv(B)) in\n              if X12 = h(Na) then\n                new sid;\n                event Request(B, A, 'WeakAuthBAAtomicNa', Na, sid);\n                event Request(B, A, 'StrongAuthBAAtomicNa', Na, sid);\n                event Secret(Na, A, B);\n                event Secret(Nb, A, B);\n                0\nprocess: \n  new dishonest;\n  out(dishonest);\n  out(priv(dishonest));\n  ! new agent;\n  event Honest(agent);\n  out(agent);\n  out(pk(priv(agent)));\n  ! (\n    A(agent)\n   | \n    B(agent)\n  )\nlemma secrecy_A_B_Na [output=[spthy]] :\n  \"All A B x #i #agA #agB. ((Honest(A) @ agA & (Honest(B) @ agB & Secret(x, A, B) @ i)) ==> not(Ex #j. KU(x) @ j))\"\nlemma secrecy_A_B_Nb [output=[spthy]] :\n  \"All A B x #i #agA #agB. ((Honest(A) @ agA & (Honest(B) @ agB & Secret(x, A, B) @ i)) ==> not(Ex #j. KU(x) @ j))\"\nlemma weakAuth_A_B_Nb [output=[spthy, proverif]] :\n  \"All A B WeakAuthABAtomicNb t #i sid #ag. ((Honest(A) @ ag & Request(B, A, WeakAuthABAtomicNb, t, sid) @ i) ==> Ex #j. Witness(A, B, WeakAuthABAtomicNb, t) @ j)\"\nlemma weakAuth_B_A_Na [output=[spthy, proverif]] :\n  \"All B A WeakAuthBAAtomicNa t #i sid #ag. ((Honest(B) @ ag & Request(A, B, WeakAuthBAAtomicNa, t, sid) @ i) ==> Ex #j. Witness(B, A, WeakAuthBAAtomicNa, t) @ j)\"\nlemma strongAuth_A_B_Nb [output=[spthy]] :\n  \"All A B StrongAuthABAtomicNb t #i sid #ag. ((Honest(A) @ ag & Request(B, A, StrongAuthABAtomicNb, t, sid) @ i) ==> Ex #j. (Witness(A, B, StrongAuthABAtomicNb, t) @ j & not(Ex #i1 #i2 sid1 sid2. ((Request(B, A, StrongAuthABAtomicNb, t, sid1) @ i1 & Request(B, A, StrongAuthABAtomicNb, t, sid2) @ i2) & not(sid1 = sid2)))))\"\nlemma strongAuth_B_A_Na [output=[spthy]] :\n  \"All B A StrongAuthBAAtomicNa t #i sid #ag. ((Honest(B) @ ag & Request(A, B, StrongAuthBAAtomicNa, t, sid) @ i) ==> Ex #j. (Witness(B, A, StrongAuthBAAtomicNa, t) @ j & not(Ex #i1 #i2 sid1 sid2. ((Request(A, B, StrongAuthBAAtomicNa, t, sid1) @ i1 & Request(A, B, StrongAuthBAAtomicNa, t, sid2) @ i2) & not(sid1 = sid2)))))\"\nexport queries :\n \"\n query x:bitstring, A:bitstring, B:bitstring; ((event(eHonest(A)) && event(eHonest(B))) && event(attacker(x))).\n query x:bitstring, A:bitstring, B:bitstring; ((event(eHonest(A)) && event(eHonest(B))) && event(attacker(x))).\n query A:bitstring, StrongAuthABAtomicNb:bitstring, B:bitstring, sid:bitstring, t:bitstring; ((event(eHonest(A)) && inj-event(eRequest(B, A, StrongAuthABAtomicNb, t, sid))) ==> inj-event(eWitness(A, B, StrongAuthABAtomicNb, t))).\n query B:bitstring, StrongAuthBAAtomicNa:bitstring, A:bitstring, sid:bitstring, t:bitstring; ((event(eHonest(B)) && inj-event(eRequest(A, B, StrongAuthBAAtomicNa, t, sid))) ==> inj-event(eWitness(B, A, StrongAuthBAAtomicNa, t))).\n \"\nend\n"
      Left m -> m @?= ""
