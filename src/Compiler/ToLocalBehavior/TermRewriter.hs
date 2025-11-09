{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToLocalBehavior.TermRewriter where

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

-- | Analyze a list of states in Phase 1.
--   * Iteratively applies rewrite rules to terms in the frame.
--   * Collects labels of destructed terms and destructor applications.
analyzePhase1States :: Int -> TRR.Description -> [State] -> ([State], [DestructorApp])
analyzePhase1States freshI description states =
  let (states', dApps) = unzip $ map (analyzePhase1State freshI description) states
      destructors = combineDestructors dApps
   in (states', destructors)

-- | Analyze a single state in Phase 1.
--   * Iteratively applies rewrite rules to terms in the frame.
--   * Collects labels of destructed terms and destructor applications.
analyzePhase1State :: Int -> TRR.Description -> State -> (State, [DestructorApp])
analyzePhase1State freshI description state =
  let analyseState = newAnalyseState (prevDestructed state) (Map.keys frame)
      (state', destructedLabels, destructors) = analyzePhase1 freshI description state analyseState
      state'' = insertDestructions destructedLabels state'
   in (state'', destructors)
  where
    frame = LBT.frame state

-- | Combine multiple destructors by concatenating them.
combineDestructors :: [[DestructorApp]] -> [DestructorApp]
combineDestructors = removeDuplicateDestructorApps . concat

-- | Initialize the label tracker with a list of labels to analyze.
newAnalyseState :: Set.Set Label -> [Label] -> AnalyseState
newAnalyseState prevDestructed labels =
  let newL = Set.difference (Set.fromList labels) prevDestructed
  in AnalyseState {lnew = Set.toList newL, lhold = [], ldone = []}


--------------------------------------------------------------------------------
-- Phase 1: Rewriting Terms
--------------------------------------------------------------------------------

-- | Phase 1: Iteratively analyze all terms in the frame.
--   * Adds derivable subterms to the frame.
--   * Collects the labels of destructed terms.
--   * Returns the updated frame, destructed labels, and destructor applications.
analyzePhase1 :: Int -> TRR.Description -> LBT.State -> AnalyseState -> (State, Destructed, [DestructorApp])
analyzePhase1 _ _ state (AnalyseState {lnew = []}) = (state, Set.empty, [])
analyzePhase1 freshI description state labels@(AnalyseState {lnew = xi : ln}) =
  case Map.lookup xi frame of
    Nothing -> (state, Set.empty, [])
    Just term ->
      case applyRewriteRulesToTerm freshI constructors (Map.toList rules) state xi term of
        Right (freshI', state1, xi's, destructors, sid) ->
          let analyseState =
                AnalyseState
                  { lnew = xi's ++ lhold labels ++ ln,
                    lhold = [],
                    ldone = xi : ldone labels
                  }
              state2 = addSessionID sid $ updateUnboundedTerms rules constructors state1
              (state3, destructedLabels, destructorsRes) = analyzePhase1 freshI' description (updateUnboundedTerms rules constructors state2) analyseState
           in (state3, Set.insert xi destructedLabels, destructors ++ destructorsRes)
        Left TermNotAnalyzed ->
          analyzePhase1 freshI description state $ labels {lnew = ln, ldone = xi : ldone labels}
        Left (TermNotComposable _) ->
          analyzePhase1 freshI description state $ labels {lnew = ln, lhold = xi : lhold labels}
  where
    frame = LBT.frame state
    constructors = TRR.constructors description
    rules = TRR.rewriteRules description

-- | Apply rewrite rules to a term.
applyRewriteRulesToTerm :: Int -> Constructors -> [(FUNCTIONS, RewriteRule)] -> State -> Label -> Term -> RewriteOutcome
applyRewriteRulesToTerm freshI constructors rules initialState xi term =
  case foldM step (freshI, initialState, [], [], Nothing) rules of
    Nothing -> Left (TermNotComposable term)
    Just (_, _, [], [], _) -> Left TermNotAnalyzed
    Just (freshI', state, labels, dApps, sid) -> Right (freshI', state, reverse labels, reverse dApps, sid)
  where
    step :: RewriteSuccess -> (FUNCTIONS, RewriteRule) -> Maybe RewriteSuccess
    step acc@(freshI', state, labels, dApps, sid) rule =
      case applyRewriteToTermHelper freshI' constructors rule state xi term of
        Left (TermNotComposable _) -> Nothing
        Left TermNotAnalyzed -> return acc
        Right (xi', newTerm, destructor, sid') ->
          let frame' = Map.insert xi' newTerm (frame state)
           in return (freshI' + 1, state {frame = frame'}, xi' : labels, destructor : dApps, sid <|> sid')

-- | Apply a single rewrite rule to a term.
applyRewriteToTermHelper :: Int -> Constructors -> (FUNCTIONS, RewriteRule) -> State -> Label -> Term -> Either RuleApplicationError SingleRewriteSuccess
applyRewriteToTermHelper freshI constructors (destructor, (rewriteTerms, replacement)) state xi term =
  case rewriteTerms of
    [key, rwTerm] -> applyPossiblyKeyedRewrite freshI constructors destructor (Just key) rwTerm replacement state xi term
    [rwTerm] -> applyPossiblyKeyedRewrite freshI constructors destructor Nothing rwTerm replacement state xi term
    _ -> Left TermNotAnalyzed

-- | Apply a rewrite rule to a term with a possible key.
applyPossiblyKeyedRewrite :: Int -> Constructors -> FUNCTIONS -> Maybe RewriteTerm -> RewriteTerm -> Replacement -> State -> Label -> Term -> Either RuleApplicationError SingleRewriteSuccess
applyPossiblyKeyedRewrite freshI constructors destructor key rewriteTerm replacement state xi term = do
  (keyTerm, replacementTerm) <-
    either (const $ Left TermNotAnalyzed) Right $ -- TODO: is TermNotAnalyzed the right error?
      do
        binding <- matchPatternSingle rewriteTerm term
        keyT <- traverse (applyBinding binding) key
        replT <- applyBinding binding replacement
        return (keyT, replT)

  let newLabel = generateLabel freshI

  subterms <- case keyTerm of
    Just k
      | Just l <- compose constructors state k -> return [l, LAtom xi]
      | otherwise -> Left (TermNotComposable k)
    Nothing -> return [LAtom xi]

  let sid = case destructor of
        DSID -> Just replacementTerm
        _ -> Nothing

  return
    ( newLabel,
      replacementTerm,
      DestructorApp
        { dlabel = newLabel,
          ddestructor = destructor,
          dsubterms = subterms
        },
      sid
    )

removeDuplicateDestructorApps :: [DestructorApp] -> [DestructorApp]
removeDuplicateDestructorApps = go Set.empty
  where
    go _ [] = []
    go seen (dApp@(DestructorApp {dlabel = l, ddestructor = d, dsubterms = s}) : xs)
      | Set.member (l, d, s) seen = go seen xs
      | otherwise = dApp : go (Set.insert (l, d, s) seen) xs

-- | Generate a fresh label deterministically based on index.
generateLabel :: Int -> Label
generateLabel i = "X" `T.append` T.pack (show i)