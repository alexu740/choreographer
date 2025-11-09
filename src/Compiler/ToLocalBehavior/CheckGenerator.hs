{-# LANGUAGE TupleSections #-}

module Compiler.ToLocalBehavior.CheckGenerator where

import Types.Simple (Constructors, FUNCTIONS (..), Function, )
import Types.Choreography (Term (..))
import Types.LocalBehavior (Label, Recipe (LAtom, LComp))
import Types.Rewrite (Replacement, RewriteRule, RewriteTerm (..), RuleApplicationError (..), Destructed, DestructorApp (..), State(..), Checks, RewriteSuccess, RewriteOutcome, SingleRewriteSuccess, AnalyseState(..))
import qualified Types.Rewrite as TRR
import qualified Types.Rewrite as LBT
import Compiler.ToLocalBehavior.RecipeUtility ( compose, composeSet )
import Choreography.Frame (applyBinding, matchPatternSingle)
import Choreography.State
    ( insertDestructions,
      insertChecks,
      updateUnboundedTerms,
      addSessionID ) 

import Syntax.Util(top)
import Control.Applicative (Alternative ((<|>)))
import Control.Monad (foldM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T

--------------------------------------------------------------------------------
-- Top-level Analysis Functions
--------------------------------------------------------------------------------

-- | Analyze a list of states in Phase 2.
--   * Generates checks for compositional equivalences and key matches.
--   * Returns the updated checks and states.
analyzePhase2States :: TRR.Description -> [State] -> ([State], Checks)
analyzePhase2States description states =
  let (states', checks) = unzip $ map (analyzePhase2State description) states
      combinedChecks = combineChecks checks
   in (states', combinedChecks)

-- | Analyze a single state in Phase 2.
--   * Generates checks for compositional equivalences and key matches.
--   * Returns the updated checks and 
analyzePhase2State :: TRR.Description -> State -> (State, Checks)
analyzePhase2State description state =
  let frame = LBT.frame state
      nonDestructedLabels = Set.toList $ Map.keysSet frame `Set.difference` prevDestructed state
      checks = analysisPhase2 (TRR.constructors description) state nonDestructedLabels
      newChecks = checks `checkDifference` prevChecks state

      state' = insertChecks newChecks state
   in (state', newChecks)

--------------------------------------------------------------------------------
-- Phase 2: Generate Checks
--------------------------------------------------------------------------------

-- | Phase 2: For each term in the frame, generate additional checks:
--   * Check for compositional equivalences.
--   * Check that keys match expected pairings.
analysisPhase2 :: Constructors -> State -> [Label] -> Checks
analysisPhase2 _ _ [] = []
analysisPhase2 constructors state (xi : xs) =
  case Map.lookup xi frame of
    Nothing -> [] -- will never reach here
    Just t ->
      let checkKey = keyCheck constructors xi state t
          checkSimilar = similarChecks constructors state t
          checksAcc = checkKey ++ checkSimilar
       in checksAcc ++ analysisPhase2 constructors state xs
  where
    frame = LBT.frame state

-- | Generate checks for terms that are composable in multiple ways.
similarChecks :: Constructors -> State -> Term -> Checks
similarChecks constructors state term =
  case Set.toList (composeSet constructors state term) of
    [] -> []
    x : xs -> map (x,) xs

-- | Generate key-matching checks for decryption operations.
--   For example, if analyzing INV(k), ensure CRYPT(k, ...) decrypts appropriately.
keyCheck :: Constructors -> Label -> State -> Term -> Checks
keyCheck constructors xi state term =
  case term of
    Composed INV [k] ->
      ( case compose constructors state k of
          Nothing -> []
          Just l -> [(LComp VCRYPT [LAtom xi, LComp CRYPT [l, LAtom top]], LAtom top)]
      )
    _ -> []

--------------------------------------------------------------------------------
-- Miscellaneous Utilities
--------------------------------------------------------------------------------

-- | Combine multiple checks by concatenating them and removing duplicates.
combineChecks :: [Checks] -> Checks
combineChecks = removeDuplicateChecks . concat

-- | Remove duplicates from a list.
removeDuplicateChecks :: Checks -> Checks
removeDuplicateChecks = go Set.empty
  where
    go _ [] = []
    go seen ((a, b) : ls)
      | Set.member (a, b) seen || Set.member (b, a) seen = go seen ls
      | otherwise = (a, b) : go (Set.insert (a, b) seen) ls

checkDifference :: Checks -> Checks -> Checks
checkDifference allChecks prevChecks =
  let prevChecksSet = Set.fromList prevChecks
   in go prevChecksSet allChecks
  where
    go _ [] = []
    go prev ((a, b) : ls)
      | Set.member (a, b) prev || Set.member (b, a) prev = go prev ls
      | otherwise = (a, b) : go prev ls
