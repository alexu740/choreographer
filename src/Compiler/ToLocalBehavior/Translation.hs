{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Compiler.ToLocalBehavior.Translation where

import Types.Simple (FUNCTIONS(..), Constructors)
import Types.LocalBehavior (LocalBehavior (..))
import Types.Choreography (Agent, Choreography (..), Term (..), CDefault (..), Atomic(..))
import Types.Rewrite (FrameError(..), TranslationError(..), State, Description(..), RewriteRules, TranslationResult)
import Types.Signatures (LocalBehaviorTranslatorFunction)
import Types.ChoreographyProtocolShell(ProtocolDescription (protocolRoles, protocolChoreo, protocolAlgebra))

import Choreography.State (mkState)
import Syntax.Util (stdConstructors, getConstructors, getAgentRoleKnowledge)

import qualified Types.Rewrite as Description
import qualified Types.Rewrite as State
import qualified Choreography.Frame as Frame

import Choreography.Enricher (stdRewriteRules)

import Compiler.ToLocalBehavior.TranslationCases.StateHint (translateStateHint)
import Compiler.ToLocalBehavior.TranslationCases.Lock (translateLock)
import Compiler.ToLocalBehavior.TranslationCases.Send (translateSend, translateSendState)
import Compiler.ToLocalBehavior.TranslationCases.Receive (translateReceive)

import Debug.Trace (trace, traceM, traceShowId)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)

import qualified Data.Text as T
import qualified Data.Map as Map

translateForAllRoles :: Constructors -> ProtocolDescription -> Either TranslationError [(State, LocalBehavior)]
translateForAllRoles constructors protocolSpecification = do
  let initialStates = mapAgentDescriptionsToInitialStates constructors protocolSpecification
  let (agentDescription, agentState) = initialStates !! 0 -- "a"
  let translated = translateToLocalBehavior agentDescription [(agentState, protocolChoreo protocolSpecification)]
  seq translated traceM("---")

  case translated of
    Left err   -> Left err
    Right lb   -> Right [(agentState, lb)]

mapAgentDescriptionsToInitialStates :: Constructors -> ProtocolDescription -> [(Description, State)]
mapAgentDescriptionsToInitialStates constructors protocolDesc =
  let roles = protocolRoles protocolDesc
      initial (ag, roleK) =
        ( Description
            { agent = ag,
              constructors = Map.unions [stdConstructors, getConstructors protocolDesc, constructors],
              rewriteRules = protocolAlgebra protocolDesc
            },
          mkState roleK
        )
  in map initial (getAgentRoleKnowledge roles)

translateToLocalBehavior :: LocalBehaviorTranslatorFunction
translateToLocalBehavior description fcsUnpruned = do
  translateWithDescription description fcsUnpruned

-- | Translates a list of frame-choreography pairs into a local behavior given the agent and previous checks.
--
-- Returns
-- * A local behavior.
translateWithDescription :: LocalBehaviorTranslatorFunction
translateWithDescription description fcsUnpruned =
  let thisAgent = Description.agent description
      fcsPruned = prunefcs thisAgent fcsUnpruned
  in case fcsPruned of
    (_, Nil) : fsc' -> if allNil fsc' then Right LNil else Left $ DifferentTypes "nil"
    (_, Lock lockAgent _) : _ -> translateLock translateWithDescription lockAgent description fcsPruned
    (_, StateHint _ _)    : _ -> translateStateHint translateWithDescription description fcsPruned
    (_, Interaction fromAgent toAgent tcs _) : _
      | fromAgent == thisAgent, 
        toAgent == dummyAgent  -> translateSendState translateWithDescription (length tcs) description fcsPruned
      | fromAgent == thisAgent ->  translateSend translateWithDescription (length tcs) description fcsPruned -- Send
      | toAgent == thisAgent   -> 
        let l = Frame.newLabel (map (State.frame . fst) fcsPruned) 
        in translateReceive translateWithDescription l description fcsPruned -- Receive
      | otherwise -> Left Unreachable -- agent not involved : should not be possible after prune
    _ -> Left UndefinedError

-- | Prunes a list of frame-choreography pairs.
--   Removes iteratively all Interactions where the given agent is not involved until
--   a suitable Interaction or a non-Interaction Choreography is reached
-- Returns
-- * A valid list of frame-choreography pairs.
prunefcs :: Agent -> [(State.State, Choreography)] -> [(State.State, Choreography)]
prunefcs agent = concatMap (prunefc agent)

-- | Prunes a single frame-choreography pair.
--   I.e. removes all communication where the given agent is not involved.
--
-- Returns
-- * A pruned list of frame-choreography pairs.
prunefc :: Agent -> (State.State, Choreography) -> [(State.State, Choreography)]
prunefc agent (state, choreo@(Interaction fromAgent toAgent tcs _))
  | agent /= fromAgent && agent /= toAgent =
      prunefcs agent $ map ((state,) . snd) tcs
  | otherwise = [(state, choreo)]
prunefc _ fc = [fc]

-- | Checks if all of the given choreographies are Nil.
allNil :: [(State.State, Choreography)] -> Bool
allNil = all (\(_, c) -> c == Nil)

-- | A dummy agent used for session handling.
dummyAgent :: Agent
dummyAgent = "DUMMY"

translateWith :: Agent -> Constructors -> RewriteRules -> [(State.State, Choreography)] -> TranslationResult LocalBehavior
translateWith agent constructors rewriteRules =
  translateWithDescription
    ( Description.Description
        { Description.agent = agent,
          Description.constructors = stdConstructors `Map.union` constructors,
          Description.rewriteRules = rewriteRules
        }
    )

translate :: Agent -> [(State.State, Choreography)] -> TranslationResult LocalBehavior
translate agent =
  translateWithDescription
    ( Description.Description
        { Description.agent = agent,
          Description.constructors = stdConstructors,
          Description.rewriteRules = stdRewriteRules
        }
    )