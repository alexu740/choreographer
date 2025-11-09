{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToLocalBehavior.TranslationCases.Send where

import Types.Simple (FUNCTIONS(..))
import Types.LocalBehavior (LocalBehavior (..))
import qualified Types.Rewrite as State
import qualified Types.Rewrite as Description
import Types.Choreography (Agent, Term (..), Atomic (..),  Choreography (..))
import Types.Rewrite (FrameError(..), TranslationError(..), State (sessionID),TranslationResult)
import Types.Signatures (LocalBehaviorTranslatorFunction)

import Compiler.ToLocalBehavior.RecipeUtility (constructAllRecipes, removeRecipesFromState)
import qualified Data.List as List

import Debug.Trace (trace, traceM, traceShowId)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow, pPrint)

-- | Translates a send given the sending agent, number of choices, and a list of frame-choreography pairs.
--
-- Returns
-- * 'Right' the resulting local behavior.
-- * 'Left' error if the extraction of sends fail, or no common recipe(s).
translateSend :: LocalBehaviorTranslatorFunction -> Int -> Description.Description -> [(State.State, Choreography)] -> TranslationResult LocalBehavior
translateSend translateWithDescription noChoices description fcs = do
  let n = length fcs
  (states, choreos, terms) <- extractSend (Description.agent description) noChoices fcs -- choreos = [..., [D_1^i, ..., D_m^i], ...]  
  recipes <- constructAllRecipes (Description.constructors description) states terms
  let nextChoreos = List.transpose choreos -- [..., [D_j^1, ..., D_j^n], ...]
  let nextfcs = map (states `zip`) nextChoreos -- [..., [(F1, D_j^1), ..., (Fn, D_j^n)], ...]
  let next = map (translateWithDescription description) nextfcs
  nextSeq <- sequence next
  return (LSend $ recipes `zip` nextSeq)


-- | Translates a send given the sending agent, number of choices, and a list of frame-choreography pairs.
--
-- Returns
-- * 'Right' the resulting local behavior.
-- * 'Left' error if the extraction of sends fail, or no common recipe(s).
translateSendState :: LocalBehaviorTranslatorFunction -> Int -> Description.Description -> [(State.State, Choreography)] -> TranslationResult LocalBehavior
translateSendState translateWithDescription noChoices description fcs = do
  (states, choreos, terms) <- extractSend (Description.agent description) noChoices fcs -- choreos = [..., [D_1^i, ..., D_m^i], ...]
  recipes <- constructAllRecipes (Description.constructors description) states terms
  let nextChoreos = List.transpose choreos -- [..., [D_j^1, ..., D_j^n], ...]
  let states' = zipWith removeRecipesFromState states recipes
  let nextfcs = map (states' `zip`) nextChoreos -- [..., [(F1, D_j^1), ..., (Fn, D_j^n)], ...]
  let next = map (translateWithDescription description) nextfcs
  nextSeq <- sequence next
  return (LSend $ recipes `zip` nextSeq)

-- | Extracts all send-substructures and send-terms for a 'Interaction' structure
--   in a list of frame and choreography-lists pairs, and a list of term-lists.
--
-- Returns
-- * 'Right' pairs of frame and choreography-lists, and lists of term-lists if all checks pass.
-- * 'Left' error if:
--    * Any block is not a 'Interaction'.And
--    * The send agents are different.
--    * The number of choices are different.
extractSend :: Agent -> Int -> [(State.State, Choreography)] -> TranslationResult ([State.State], [[Choreography]], [[Term]])
extractSend _ _ [] = return ([], [], [])
extractSend agent m ((state, Interaction agentFrom _ tcs _) : fcs)
  | agent /= agentFrom = Left $ DifferentAgents agent agentFrom
  | length tcs /= m = Left DifferentBranchLength
  | otherwise =
      do
        (states, choreos, terms) <- extractSend agent m fcs
        return (state : states, map snd tcs : choreos, map fst tcs : terms)
extractSend _ _ _ = Left $ DifferentTypes "send"