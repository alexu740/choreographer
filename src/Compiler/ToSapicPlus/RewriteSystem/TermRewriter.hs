{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Compiler.ToSapicPlus.RewriteSystem.TermRewriter where

import Compiler.ToSapicPlus.RewriteSystem.Rule (verifierRules)
import Compiler.ToSapicPlus.RewriteSystem.RewriteReceipt (RewriteReceipt(..))
import Compiler.ToSapicPlus.RewriteSystem.EquationalTheoryExtension (termIsComposableModuloTheory, operations, findEquivalenceClass)

import Compiler.ToSapicPlus.RewriteSystem.RewriteSystem(
  RewriteSystem(..), getRewriteSystem
  )

import Compiler.ToSapicPlus.SFrame(
    SFrame(..),
    insertTermInFrameWithReturn, insertDeconstructedEntry, insertReceipt,
    insertBoundedEntry,
    bindIfUnique
  )
import Compiler.ToSapicPlus.RecipeUtility (compose, recipeToTerm)

import Types.ChoreographyProtocolShell (ProtocolDescription)
import Types.Sapic (SRecipe, SVariable, STerm(..), RTerm(..), Rule(..))
import Types.Simple (Function, FUNCTIONS(..))
import Types.Choreography (Term(..))

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Text (Text)
import Data.Traversable (mapAccumL)
import Data.List (find)
import Data.Maybe (fromJust, fromMaybe)
import Control.Monad (guard, foldM)
import Data.Maybe (mapMaybe)

import Debug.Trace (trace, traceM, traceShowId, traceShow)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)


type RSubst = Map.Map Text Term

-- | Analyze a list of states in Phase 1.
--   * Iteratively applies rewrite rules to terms in the frame.
--   * Collects labels of destructed terms and destructor applications.
analyzePhase1States :: ProtocolDescription -> [SFrame] -> ([SFrame], [RewriteReceipt])
analyzePhase1States description frames =
    let rewriteSystem = getRewriteSystem description
        (states', receipts) = unzip $ map (discoverNewTermsInFrame description rewriteSystem []) frames
        receipts' = combineDestructors receipts
    in (states', receipts')

combineDestructors :: [[RewriteReceipt]] -> [RewriteReceipt]
combineDestructors = removeDuplicateRewriteReceipts . concat

removeDuplicateRewriteReceipts :: [RewriteReceipt] -> [RewriteReceipt]
removeDuplicateRewriteReceipts = go Set.empty
  where
    -- dedupe on (frameKey, ruleFunction, subject)
    go _ [] = []
    go seen (r@RewriteReceipt{ frameKey = k, ruleFunction = d, subjectRecipe = s } : rs)
      | Set.member (k, d, s) seen = go seen rs
      | otherwise = r : go (Set.insert (k, d, s) seen) rs
-- 


discoverNewTermsInFrame :: ProtocolDescription -> RewriteSystem -> [RewriteReceipt] -> SFrame -> (SFrame, [RewriteReceipt])
discoverNewTermsInFrame description rs existingReceipts frame  = do
  let decomposableTerms = findTermsThatCanBeDeconstructed frame
  let rules = systemRules rs
  let discoveredTerms = [(result, rule, term) | term <- decomposableTerms , rule <- rules , Just result <- [applyRule rs frame rule term]]
  case discoveredTerms of
    [] -> (frame, [])
    _ -> -- in case we found terms, 
      -- We need to get those terms that were actually deconstructed
      -- Think if it is actually needed to keep track of those.
      -- Maybe not all rules that are relevant for a term can be applied at the same time.
      -- Fx. d(c(x,y,z),y)->x and d(c(x,y,z),x)->z
      -- A bit absurd, but you need to first apply rule 1, to then apply rule 2, given one knows only "y"
      -- makes more sense to track rule-term combinations as those occur only once
      let (frame', newReceipts) = mapAccumL (updateFrameAndWriteOutReceipt description) frame discoveredTerms
          receiptsSoFar = existingReceipts ++ newReceipts
          (updatedFrame, allReceipts) = discoverNewTermsInFrame description rs receiptsSoFar frame' 
      in (updatedFrame, receiptsSoFar ++ allReceipts)

updateFrameAndWriteOutReceipt :: ProtocolDescription -> SFrame -> ((Term, [(RTerm, Term)]), Rule, Term) -> (SFrame, RewriteReceipt)
updateFrameAndWriteOutReceipt description frame ((resultTerm, ruleArgToTermMap), rule, term) = do
  let (frame', newKey) = insertTermInFrameWithReturn frame resultTerm
  let deconstructedTermFrameKey = fromJust (getFrameKeyForTerm frame' term)
  let frame'' = insertDeconstructedEntry frame' deconstructedTermFrameKey
  let frame''' = bindIfUnique frame'' newKey resultTerm
  
  let receipt = RewriteReceipt {
    frameKey = newKey,
    subject = term,
    rule = rule,
    subjectRecipe = deconstructedTermFrameKey,
    ruleFunction = destructor rule,
    ruleArgsToTermsMap = ruleArgToTermMap,
    ruleArgsToRecipeMap = translateToRecipeMap description ruleArgToTermMap frame'''
  }
  let frame'''' = insertReceipt frame''' receipt
  (frame'''', receipt)

translateToRecipeMap :: ProtocolDescription -> [(RTerm, Term)] -> SFrame -> [(RTerm, STerm)]
translateToRecipeMap description termMap frame = 
    mapMaybe
    (\(rpat, t) -> (rpat,) . recipeToTerm <$> compose description frame t)
    termMap

toRecipe :: SFrame -> Term -> STerm
toRecipe fr t =
  case getFrameKeyForTerm fr t of
    Just k  -> TVariable k
    Nothing ->
      case t of
        Atomic _ ->
          error ("translateToRecipeMap: term not composable from frame: " ++ show t)
        Composed f ts ->
          TFunction f (map (toRecipe fr) ts)

-- validation and prerequisites --
-- find terms in frame that can be deconstructed
findTermsThatCanBeDeconstructed :: SFrame -> [Term]
findTermsThatCanBeDeconstructed frame =
  let allFrameKeys = Map.keysSet (mapping frame)
      respectiveTerms = map (\k -> mapping frame Map.! k) (Set.toList allFrameKeys)
  in List.filter isTermPotentiallyDecomposable respectiveTerms

isTermPotentiallyDecomposable :: Term -> Bool
isTermPotentiallyDecomposable (Atomic x) = False
isTermPotentiallyDecomposable (Composed f []) = False
isTermPotentiallyDecomposable (Composed _ (_:_)) = True
-- validation and prerequisites --
----------------------------------
-- rule handling --
doesRuleContainConstructor :: Rule -> (Function, [Term]) -> Bool
doesRuleContainConstructor rule (termConstructorSymbol, termArgs) =
  -- take all rule args and find only those that are functions of same type like our term
  -- function symbols and arity must match. additionally, the result symbol must be part of
  -- the rule function that matches our term
  case [ps | RConstr g ps <- args rule, g == termConstructorSymbol] of
    [ps] ->
      let arityMatches = length ps == length termArgs
          resultOccurs = result rule `elem` ps
      in arityMatches && resultOccurs
    _ -> False

isMatchRuleShape :: Rule -> Term -> Bool
isMatchRuleShape rule term =
  case term of 
    (Atomic _) -> False
    (Composed f args) -> doesRuleContainConstructor rule (f,args)
    
alreadyDecomposed :: Rule -> Term -> [RewriteReceipt] -> Bool
alreadyDecomposed rule term =
  any (\ r -> ruleFunction r == destructor rule && subject r == term)

applyRule :: RewriteSystem -> SFrame -> Rule -> Term -> Maybe (Term, [(RTerm, Term)])
applyRule rs frame rule term =
  let alreadyDone = alreadyDecomposed rule term (receipts frame)
      matchesRule = isMatchRuleShape rule term
  in 
    if alreadyDone 
      then Nothing 
      else (if matchesRule then applyRuleSafely rs frame rule term else Nothing)

applyRuleSafely :: RewriteSystem -> SFrame -> Rule -> Term ->  Maybe (Term, [(RTerm, Term)])
applyRuleSafely rs frame rule term =
  case args rule of
    [_] -> do
      result <- applyProjection rule term
      Just (result, [])
    (_:_) -> applyDestruction rs frame rule term
    _ -> Nothing
-- rule handling --
----------------------
-- rule application --
-- Retrieves the element based on index from the term args (term = Composed f [args])
-- The index is purely based on where the "result" symbol occurs in the rule.
applyProjection :: Rule -> Term -> Maybe Term
applyProjection rule term = 
  case (args rule, term) of
    ([RConstr f ps], Composed f' rs)
      | f == f' && length ps == length rs ->
          case result rule of
            RVar x ->
              case [ i | (i, RVar y) <- zip [0..] ps, y == x ] of
                [i] -> Just (rs !! i)
                _ -> Nothing
            _ -> Nothing
    _ -> Nothing

applyDestruction :: RewriteSystem -> SFrame -> Rule -> Term ->  Maybe (Term, [(RTerm, Term)])
applyDestruction rs frame rule term = do
  (necessarySubterms, ruleVarToTermSubstitutions, mapRulePartsAsTerms) <- prepareDestructionRequirements rule term
  case necessarySubterms of
    -- for destructors, there must always be at least one check
    -- due to there always being more arguments in the rule than
    -- the constructor part itself.
    [] -> Nothing 
    subterms -> do
      guard (all (isTermComposableGivenFrame rs frame) subterms)
      result <- instantiateResult (result rule) ruleVarToTermSubstitutions
      Just (result, mapRulePartsAsTerms)

-- Based on substitution from rule, 
-- return the part of the rule that corresponds to the result
instantiateResult :: RTerm -> RSubst -> Maybe Term
instantiateResult t sigma = substRTerm sigma t
-- rule application --

----------------------
-- | Returns something a la Just [Composed INV [Atomic "Nb"]]
-- deducts checks that must be fulfilled against existing knowledge
-- Fx. d(c(x,k), inv(k))=x and term: c(Na, Nb)
-- This function will find that inv(Nb) must be composable within the 
-- knowledge of the agent (frame) in order for the rule to be applied
-- this means that a list of subterms must be composable
prepareDestructionRequirements :: Rule -> Term -> Maybe ([Term], RSubst, [(RTerm, Term)])
prepareDestructionRequirements rl term = do
  (indexOfConstructor, sigma0) <- matchHeadAndSigma rl term
  let otherArgsOfRuleBesideConstructor = take indexOfConstructor (args rl)
               ++ drop (indexOfConstructor + 1) (args rl)

  requirements <- mapM (substRTerm sigma0) otherArgsOfRuleBesideConstructor
  let mapRulePartsAsTerms = [  (arg , t)
                        | arg <- otherArgsOfRuleBesideConstructor
                        , Just t <- [substRTerm sigma0 arg]
                      ]
  Just (requirements, sigma0, mapRulePartsAsTerms)

matchHeadAndSigma :: Rule -> Term -> Maybe (Int, RSubst)
matchHeadAndSigma rl term = case term of
  Composed f rs ->
    let indexAndArgsOfConstructorPartOfTheRule =
          [ (i, ps)
          | (i, RConstr g ps) <- zip [0..] (args rl)
          , g == f
          , length ps == length rs
          ]
    in case indexAndArgsOfConstructorPartOfTheRule of
        -- allow only one constructor in rule, otherwise rull ill define and yields nothing
         [(i, ps)] -> (i,) <$> buildSigmaDeep (RConstr f ps) (Composed f rs)
         _ -> Nothing
  _ -> Nothing

-- | Builds a mapping (RSubst) between the args in the constructor rule and actual term
-- fx. rule: d(c(x,k), inv(k))=x and term: c(Na, Nb)
-- This will make the mapping
-- The rule can also make nested lookups, but rules like that are not supported as of yet
-- x -> Na
-- k -> Nb
buildSigmaDeep :: RTerm -> Term -> Maybe RSubst
buildSigmaDeep (RVar x) r = Just (Map.singleton x r)
buildSigmaDeep (RConstr f ps) (Composed g rs)
  | f == g && length ps == length rs =
      foldM (\acc (p,r') -> Map.union acc <$> buildSigmaDeep p r')
            Map.empty
            (zip ps rs)
  | otherwise = Nothing
buildSigmaDeep _ _ = Nothing

-- | Tries to create target terms that are needed for a rule.
-- Only for other arguments of the rule, beside the constructor itself.
-- Fx. d(c(x,k), inv(k))=x and term: c(Na, Nb)
-- With the mapping previously created with buildSigmaDeep:
-- x -> Na
-- k -> Nb
-- prepareDestructionRequirements will call this with Rule terms: inv(k)
-- This function will then apply the mapping in order to yield inv(Nb)
-- Sigma stands for substitution mapping
substRTerm :: RSubst -> RTerm -> Maybe Term
substRTerm sigma = go
  where
    go (RVar x) = Map.lookup x sigma
    go (RConstr f ps) = Composed f <$> traverse go ps

--- match against frame knowledge
getFrameKeyForTerm :: SFrame -> Term -> Maybe SVariable
getFrameKeyForTerm frame term =
  fmap fst (List.find ((== term) . snd) (Map.toList (mapping frame)))

isTermComposableGivenFrame :: RewriteSystem -> SFrame -> Term -> Bool
isTermComposableGivenFrame rs frame term =
  case term of
    Atomic k ->
      case getFrameKeyForTerm frame (Atomic k) of
        Just k -> True
        Nothing -> False
    (Composed constructor []) -> do
      let allowedContructors = Set.toList $ Map.keysSet $ systemConstructors rs
      constructor `elem` allowedContructors
    composedTerm@(Composed constructor args) ->
      case getFrameKeyForTerm frame composedTerm of
        Just k -> True
        _ -> do
          let allowedContructors = Set.toList $ Map.keysSet $ systemConstructors rs
          let operationSymbols = map fst operations
          if constructor `elem` (allowedContructors ++ operationSymbols)
            --then all (isTermComposableGivenFrame rs frame) args
            then termIsComposableModuloTheory rs frame composedTerm
            else False
--- match against frame knowledge ---



-----------------------
--------------------------------------- Apply frame adapted to new term rewriting

applyFrame :: ProtocolDescription -> SFrame -> STerm -> Either Text Term
applyFrame description frame recipe =
  case recipe of
    TVariable l ->
      case Map.lookup l (mapping frame) of
        Just t -> Right t
        Nothing -> Left "UndefinedLabel (frame, variable not found)"

    TFunction f rs -> do
      rs' <- traverse (applyFrame description frame) rs
      let rules = systemRules (getRewriteSystem description)

      case find (\r -> destructor r == f) rules of
        -- generaly compose where we succeed only if all atomic parts are present
        Nothing -> 
          case find (\r -> destructor r == f) verifierRules of
            Just rule -> do 
              sigma <- matchArgs (args rule) rs'
              Right ((rTermToTerm . result) rule)
            Nothing  -> Right (Composed f rs')
        -- relevant for the let statment constructions, 
        -- as we have destructors there
        Just rule -> do
          -- Create substitution from rule parts to termszw
          sigma <- matchArgs (args rule) rs'
          -- Instantiate the rule result using the substitution
          case substRTermToTerm sigma (result rule) of
            Just t -> Right t
            Nothing -> Left "Could not instantiate rule result"

--------------------------------------------------------------------------------
-- Matching RTerm patterns against Terms
--------------------------------------------------------------------------------

matchArgs :: [RTerm] -> [Term] -> Either Text RSubst
matchArgs ps ts
  | length ps /= length ts = Left "Arity mismatch in destructor application"
  | otherwise =
      case foldl step (Just Map.empty) (zip ps ts) of
        Just s -> Right s
        Nothing -> Left "Pattern match failed"
  where
    step :: Maybe RSubst -> (RTerm, Term) -> Maybe RSubst
    step acc (rterm, term) =
      case acc of
        Nothing -> Nothing
        Just s -> unify s rterm term

-- Apply substitution
unify :: RSubst -> RTerm -> Term -> Maybe RSubst
unify s (RVar x) t =
  case Map.lookup x s of
    Nothing -> Just (Map.insert x t s)
    Just tOld -> if tOld == t || tOld `equivalent` t then Just s else Nothing

unify s (RConstr f ps) (Composed g ts)
  | f == g && length ps == length ts =
      foldl step (Just s) (zip ps ts)
  | otherwise = Nothing
  where
    step :: Maybe RSubst -> (RTerm, Term) -> Maybe RSubst
    step acc pr = acc >>= \s' -> uncurry (unify s') pr
unify _ _ _ = Nothing

-- Equivalence modulo theory
equivalent :: Term -> Term -> Bool
equivalent a b =
  let repsA = findEquivalenceClass [] a
      repsB = findEquivalenceClass [] b
  in not . null $ [ () | x <- repsA, x `elem` repsB ]

--------------------------------------------------------------------------------
-- Instantiate an RTerm to a Term using a substitution
--------------------------------------------------------------------------------

substRTermToTerm :: RSubst -> RTerm -> Maybe Term
substRTermToTerm s = go
  where
    go (RVar x) = Map.lookup x s
    go (RConstr f ps) = Composed f <$> traverse go ps

rTermToTerm :: RTerm -> Term
rTermToTerm (RVar x) = Atomic x
rTermToTerm (RConstr f ps) = Composed f (map rTermToTerm ps)
