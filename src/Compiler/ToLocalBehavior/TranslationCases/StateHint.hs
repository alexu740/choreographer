{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToLocalBehavior.TranslationCases.StateHint where

import Types.Simple (FUNCTIONS(..))
import Types.LocalBehavior (LocalBehavior (..))
import Types.Choreography (Atomic (..), Agent, Term (..))
import Types.Signatures (LocalBehaviorTranslatorFunction)

import Types.Rewrite as Description ( Description(agent),FrameError(..), TranslationError(..),State (sessionID),TranslationResult )
import Types.Choreography as Choreography (Choreography(Interaction, StateHint))
import Types.Choreography as CDefault (CDefault(Epsilon))

import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Maybe as Maybe

-- | Translates state and choreography pairs by incorporating session information,
--   adapting the choreography accordingly for a given agent.
--   The given agents sends its session information to a 'DUMMY' agent,
--   and the 'DUMMY' agent sends back the session information to any agent in the system.
--
-- Returns:
-- * The updated version of the local behavior with state hint-interactions.
translateStateHint :: LocalBehaviorTranslatorFunction -> Description -> [(State, Choreography)] -> TranslationResult LocalBehavior
translateStateHint translateWithDescription description fcs = do
  fcs' <- extractStateHint fcs

  let agent = Description.agent description
  let getSessionID = Maybe.fromMaybe (Atomic "sessionID") . sessionID
  let sessions =
        [ (s, Map.mapMaybe (termListToSession (getSessionID s)) ts, c)
          | (s, ts, c) <- fcs'
        ]

  let enrichSession (s, ts, c) =
        let otherTs = Map.elems $ Map.delete agent ts
         in case Map.lookup agent ts of
              Nothing -> (s, addReceives agent otherTs c)
              Just t  -> (s, addInteraction agent t . addReceives agent otherTs $ c)
  let enrichedSessions = map enrichSession sessions
  translateWithDescription description enrichedSessions

-- | Extracts state hints from a list of (state, choreography) pairs.
--
-- Returns:
-- * 'Right' a list of triples (state, map of agent to terms, choreography) if all inputs are 'StateHint's.
-- * 'Left' with error if a non-'StateHint' is encountered.
extractStateHint :: [(State, Choreography)] -> TranslationResult [(State, Map.Map Agent [Term], Choreography)]
extractStateHint [] = return []
extractStateHint ((state, Choreography.StateHint stateList choreo) : fcs) = do
  fcs' <- extractStateHint fcs
  return ((state, stateList, choreo) : fcs')
extractStateHint _ = Left $ DifferentTypes "state-hint"

-- | Converts state information into a session constructor.
-- |
termListToSession :: Term -> [Term] -> Maybe Term
termListToSession sid ts = do
  body <- termListToTerm ts
  return $ Composed SESSION [sid, body]

-- | Converts a list of terms into nested 'PAIR' terms.
termListToTerm :: [Term] -> Maybe Term
termListToTerm [] = Nothing
termListToTerm [t] = Just t
termListToTerm (t : ts) = do
  rest <- termListToTerm ts
  return $ Composed PAIR [t, rest]

-- | Send state hint to a dummy agent,
--   and the dummy agent sends back the state hint to the agent.
addInteraction :: Agent -> Term -> Choreography -> Choreography
addInteraction agent t c =
  Choreography.Interaction agent dummyAgent [(t, Choreography.Interaction dummyAgent agent [(t, c)] CDefault.Epsilon)] CDefault.Epsilon

-- | Receive state hint from a dummy agent.
addReceives :: Agent -> [Term] -> (Choreography -> Choreography)
addReceives agent = foldr (\t c -> (\c' -> Choreography.Interaction dummyAgent agent [(t, c')] CDefault.Epsilon) . c) id

-- | A dummy agent used for session handling.
dummyAgent :: Agent
dummyAgent = "DUMMY"