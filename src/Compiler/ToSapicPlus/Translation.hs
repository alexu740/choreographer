{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Compiler.ToSapicPlus.Translation where

import Types.Simple (FUNCTIONS(..), Function)
import Types.LocalBehavior (LocalBehavior (..), LocalAtomic(..), Label, Recipe(..))
import Types.Choreography (Choreography(..), Agent, Term)
import Types.Sapic ( BuiltinTheory(..), SapicTranslationError, SProcess(..), STerm(..), SProtocol(..), SAgentProcess(..), SProtocolHeader(..), SFactType(..), SFactArgument(..) )
import Types.ChoreographyProtocolShell (ProtocolDescription(..), RoleInfo(..), Sigma(..))

import Debug.Trace (trace, traceM, traceShowId)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set

import Compiler.ToSapicPlus.SFrame (SFrame, emptyFrame, initializeFrame)
import Compiler.ToSapicPlus.InitialKnowledgeDistributor (getDependantRolesFromKnowledge)
import Compiler.ToSapicPlus.SyntacticSimplifier(compressIfBlocksOnSingularSyntacticBranch)
import Compiler.ToSapicPlus.RewriteSystem.RewriteSystem (RewriteSystem(..), initializeRewriteSystem, deduceTheories, collectFunctionSymbols)
import Compiler.ToSapicPlus.RewriteSystem.Rule (getUserDefinedRules, specialConstructors)
import Compiler.ToSapicPlus.SecurityGoalUtility (applyGoalsAtEndOfProtocol, pruneAuthenticationGoalsFromDescription, applyWitnessEventsFromGoals, convertSecurityGoalsToLemms, convertSecurityGoalsToProverifQueries)

import Compiler.ToSapicPlus.TranslationCases.Lock (translateLock)
import Compiler.ToSapicPlus.TranslationCases.Send (translateSend)
import Compiler.ToSapicPlus.TranslationCases.Receive (translateReceive)

translateProtocol :: ProtocolDescription -> Either SapicTranslationError SProtocol
translateProtocol description = do
  let allAgents = Set.toList (Map.keysSet (protocolRoles description))
  protocolHeader <- translateProcolHeader description
  agentProcesses <- traverse (translateAgent description) allAgents
  let mainProcess = translateMainProcess (builtins protocolHeader) description allAgents
  Right SProtocol { 
    protocolHeader = protocolHeader,
    agentProcesses = agentProcesses, 
    mainProcess = mainProcess,
    lemmas = convertSecurityGoalsToLemms description,
    queries = convertSecurityGoalsToProverifQueries description
  }

translateProcolHeader :: ProtocolDescription -> Either SapicTranslationError SProtocolHeader
translateProcolHeader description = do
  rewriteSystem <- initializeRewriteSystem description
  let constructors = Map.toList (systemConstructors rewriteSystem)
  let rules = systemRules rewriteSystem
  let builtinTheories = deduceTheories description
  let usedFunctions = collectFunctionSymbols (protocolChoreo description)
  let usedSet = Set.fromList (map T.toLower usedFunctions)
  Right SProtocolHeader {
      theory = "ChoreoTheory",
      builtins = builtinTheories,
      functions = functions usedSet (constructors ++ Map.toList specialConstructors),
      equations = getUserDefinedRules description
    }
  where 
    functions :: Set.Set T.Text -> [(FUNCTIONS, Int)] -> [(T.Text, Bool)]
    functions used = foldr step []
      where
        step :: (FUNCTIONS, Int) -> [(T.Text, Bool)] -> [(T.Text, Bool)]
        step (f, arity) acc =
          case f of
            UnDef x ->
              (x <> "/" <> T.pack (show arity), functionIsPublic x) : acc
            _ ->
              let nameTxt = T.toLower (T.pack (show f))
              in if nameTxt `Set.member` used
                  then (nameTxt <> "/" <> T.pack (show arity), functionIsPublicStd f) : acc
                  else acc
    functionIsPublic :: T.Text -> Bool
    functionIsPublic f =
      let sigma = protocolSigma description
      in f `Map.member` public sigma

    functionIsPublicStd :: FUNCTIONS -> Bool
    functionIsPublicStd PRIV = False
    functionIsPublicStd SK = False
    functionIsPublicStd _ = True

translateAgent :: ProtocolDescription -> Agent -> Either SapicTranslationError SAgentProcess
translateAgent description agent = do
  header <- translateAgentHeader description agent
  body <- translateProcessBody description agent
  Right SAgentProcess
    { processName = agent
    , processHeader = header
    , processBody = body
    }

translateAgentHeader :: ProtocolDescription -> Agent -> Either SapicTranslationError [T.Text]
translateAgentHeader description agent = Right [agent]

translateMainProcess :: [BuiltinTheory] -> ProtocolDescription -> [Agent] -> SProcess
translateMainProcess builtins description agents =
  let usesAsymmetricEncr = AsymmetricEncryption `elem` builtins
  in SNew (TName "dishonest") (
    SOut [(
      TName "dishonest",
      if usesAsymmetricEncr
        then 
          SOut [(
            TFunction PRIV [TName "dishonest"],
            SReplication (
              SNew (TName "agent")
              (
                SFact Honest [SFTerm $ TName "agent"] (
                  SOut [(
                    TName "agent",
                    SOut [(
                      TFunction PK [ TFunction PRIV [TName "agent"]],
                      SReplication (
                        SParallel (map agentInitialisation agents)
                      )
                    )]
                  )]
                )
              )
            )
          )]
          
        else
          SReplication (
            SNew (TName "agent")
            (
              SFact Honest [SFTerm $ TName "agent"] (
                SOut [(
                  TName "agent",
                  SReplication (
                    SParallel (map agentInitialisation agents)
                  )
                )]
              )
            )
          )
    )]
  )
  where
    agentInitialisation :: Agent -> SProcess
    agentInitialisation agent = SAgentInitialisation agent [TName "agent"]

---------------------------------------------------------------------------------------------
----------- Simba, it is a dark place here below, don't ever go there!----------------------------
translateProcessBody :: ProtocolDescription -> Agent -> Either SapicTranslationError SProcess
translateProcessBody description agent = do
  role <- getRole description agent
  dependantRoles <- getDependantRolesFromKnowledge agent (roleKnowledge role) description
  agentProcess <- translateChoreographyToSapicProcess description agent
  let squashedProcess = compressIfBlocksOnSingularSyntacticBranch agentProcess
  let finalProcess = addDependantAgentsToProcess squashedProcess dependantRoles
  Right finalProcess

addDependantAgentsToProcess :: SProcess -> [Agent] -> SProcess
addDependantAgentsToProcess = foldr (SIn . TVariable)

getRole :: ProtocolDescription -> Agent -> Either SapicTranslationError RoleInfo
getRole description agent =
  let allProtocolRoles = protocolRoles description
      targetRole = Map.lookup agent allProtocolRoles
  in case targetRole of
    Just role -> Right role
    Nothing -> Left $ T.pack ("Unknown agent: " ++ show agent)


translateChoreographyToSapicProcess :: ProtocolDescription -> Agent -> Either SapicTranslationError SProcess
translateChoreographyToSapicProcess description agent =
  let createAttempt = createInitialFrameChoreographyPair description agent
  in case createAttempt of
    Right (initialFrame, initialChoero) -> 
      let exec = handleFrameChoreographyCases description agent [(initialFrame, initialChoero)]
      in case exec of
        Right _ -> exec
        Left m -> Left m
    Left errorMessage -> Left errorMessage


createInitialFrameChoreographyPair :: ProtocolDescription -> Agent -> Either SapicTranslationError (SFrame, Choreography)
createInitialFrameChoreographyPair description agent = do
  role <- getRole description agent
  let initialKnowledgeTerms = roleKnowledge role
  let frameWithKnowledge = initializeFrame initialKnowledgeTerms
  let choreographyRoot = protocolChoreo description
  Right (frameWithKnowledge, choreographyRoot)


handleFrameChoreographyCases :: ProtocolDescription -> Agent -> [(SFrame, Choreography)] -> Either SapicTranslationError SProcess
handleFrameChoreographyCases description agent pairs =
  let filteredPairs = removeCommunicationStepsNotInvolvingGivenAgent agent pairs
  in case filteredPairs of
    (_, Nil) : rest -> 
      if all (\(_, c) -> c == Nil) rest
      then Right (applyGoalsAtEndOfProtocol description agent (map fst filteredPairs))
      else Left "DifferentTypes nil"
    (_, Interaction fromAgent toAgent _ _) : _
      | agent == fromAgent -> do
        let frames = map fst filteredPairs
        let description' = pruneAuthenticationGoalsFromDescription description agent frames
        let nextP = translateSend handleFrameChoreographyCases description' agent filteredPairs
        applyWitnessEventsFromGoals description agent frames nextP
      | agent == toAgent -> do
        let frames = map fst filteredPairs
        let description' = pruneAuthenticationGoalsFromDescription description agent frames
        let nextP = translateReceive handleFrameChoreographyCases description agent filteredPairs
        applyWitnessEventsFromGoals description agent frames nextP
      | otherwise -> Left "UndefinedError"
    (_, Lock lockAgent _) : _ -> do
      let frames = map fst filteredPairs
      let description' = pruneAuthenticationGoalsFromDescription description agent frames
      let nextP = translateLock handleFrameChoreographyCases description lockAgent agent filteredPairs
      applyWitnessEventsFromGoals description agent frames nextP
    _ -> Left "UndefinedError"
    
removeCommunicationStepsNotInvolvingGivenAgent :: Agent -> [(SFrame, Choreography)] -> [(SFrame, Choreography)]
removeCommunicationStepsNotInvolvingGivenAgent agent = concatMap (prunefc agent)

-- | Prunes a single frame-choreography pair.
--   I.e. removes all communication where the given agent is not involved.
--
-- Returns
-- * A pruned list of frame-choreography pairs.
prunefc :: Agent -> (SFrame, Choreography) -> [(SFrame, Choreography)]
prunefc agent (state, choreo@(Interaction fromAgent toAgent tcs _))
  | agent /= fromAgent && agent /= toAgent =
      removeCommunicationStepsNotInvolvingGivenAgent agent $ map ((state,) . snd) tcs
  | otherwise = [(state, choreo)]
prunefc _ fc = [fc]

----