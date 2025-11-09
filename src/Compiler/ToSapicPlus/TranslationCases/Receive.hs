{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToSapicPlus.TranslationCases.Receive where

import Types.Simple (Function)
import Types.Signatures (SapicTranslatorFunction)
import Types.Choreography (Agent, Choreography(..), CDefault(..), Term(..))
import Types.Sapic (RTerm(..), Rule(..), Check, SVariable, SProcess(..), SapicTranslationError, STerm(..), SPattern(..))
import Types.ChoreographyProtocolShell (ProtocolDescription)

import Compiler.ToSapicPlus.RewriteSystem.RewriteReceipt (RewriteReceipt(..))
import Compiler.ToSapicPlus.RewriteSystem.RewriteSystem (RewriteSystem(..), getRewriteSystem)
import Compiler.ToSapicPlus.RewriteSystem.TermRewriter (analyzePhase1States, applyFrame)

import Compiler.ToSapicPlus.SFrame (SFrame (mapping, prevChecks), insertTermInFrame, getLatestFrameKey, insertCheck, insertCheckAsTerms, toNameBasedSTerm, insertBoundedEntry)
import Compiler.ToSapicPlus.RecipeUtility (recipeToTerm, choreoTermToSTerm)

import Compiler.ToSapicPlus.CheckGenerator (analyzePhase2States)
import Compiler.ToSapicPlus.SyntacticSimplifier (aggregateReceiptsByContructorAndSubject, translateToSquashedProjectionGroup, receiveCaseSTermTranslation, 
  tryMarkIncomingVariableAsBounded, tryMarkSquashedProjectionVariableAsBounded)

import Data.List (find, foldl')
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Either as Either
import qualified Data.Map as Map

import Debug.Trace (trace, traceM, traceShowId, traceShow)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)


translateReceive :: SapicTranslatorFunction -> ProtocolDescription -> Agent -> [(SFrame, Choreography)] -> Either SapicTranslationError SProcess
translateReceive mainTranslationFunction description agent fcs = do
  (fds, cdefs) <- extractReceive agent fcs

  let firstFrame = (fst . head) fds
  addedVar <- getLatestFrameKey firstFrame
  let fds' = tryMarkIncomingVariableAsBounded fds addedVar firstFrame
  let firstFrame' = (fst . head) fds'
  -- TODO: Solve: Problem: translationTermShould actually be derived in this way only if there is one
  -- received term and only one branch. Fx. 2 branches can have X1 = Na and Nb.
  -- We can't decide in that case which to substitute and show (also checks will follow)
  let translationTerm = receiveCaseSTermTranslation firstFrame' addedVar

  let (states, receipts) = analyzePhase1States description (map fst fds')
  let fds1 = states `zip` map snd fds'
  localDef <- constructDefault mainTranslationFunction description agent cdefs

  let constructIfsTemp = constructReceiveIfs mainTranslationFunction description localDef agent

  if null receipts
    then
      let (states', checks) = analyzePhase2States description states
          fds2 = states' `zip` map snd fds1
      in (
        if null checks
        then do
          fds3 <- mainTranslationFunction description agent fds2
          return (SIn translationTerm fds3)
        else do
          fds3 <- constructIfsTemp checks fds1
          return (SIn translationTerm fds3)
      )
  else do
    let aggregatedReceipts = aggregateReceiptsByContructorAndSubject receipts
    fds2 <- constructReceiveTryCatch description constructIfsTemp aggregatedReceipts localDef agent fds1
    -- if fds2 starts with SLet, then we can try see if block of lets and ifs is linear
    return (SIn translationTerm fds2)


-- | Extracts all receive-substructures for a 'Interaction' structure
--   given the new label, the receiving agent, and a list of frame-choreography pairs.
--
-- Returns
-- * 'Right' a list of frame-choreography pairs.
-- * 'Left' error if any atomic is not a 'Interaction', or the receive agents are different.
extractReceive :: Agent -> [(SFrame, Choreography)] -> Either SapicTranslationError ([(SFrame, Choreography)], [(SFrame, CDefault)])
extractReceive _ [] = return ([], [])
extractReceive agent ((frame, Interaction _ toAgent tcs cdef) : tail)
  | agent /= toAgent = Left $ "DifferentAgents" <> agent <> toAgent
  | otherwise = do
      let updatedFrames = map (insertTermInFrame frame . fst) tcs -- F^i_j = F_i[ l |-> t^i_j ]
      let updatedPairs = zip updatedFrames (map snd tcs) -- [..., (F^i_j, D^i_j), ...]

      (fcs', cdefs) <- extractReceive agent tail

      return (updatedPairs ++ fcs', (frame, cdef) : cdefs)
extractReceive _ _ = Left "DifferentTypes receive"

-- Here we go through deconstructions split all frames into those who can or not provide
-- knowledge for the deconstruction to be made
-- We basically, reapply the deconstruction after filling in the recipes in the receipt.

constructReceiveTryCatch :: 
  ProtocolDescription -> 
  ([Check] -> [(SFrame, Choreography)] -> Either SapicTranslationError SProcess) -> 
  [[RewriteReceipt]] -> 
  SProcess -> 
  Agent -> 
  [(SFrame, Choreography)] -> 
  Either SapicTranslationError SProcess
constructReceiveTryCatch description constructIfsTemp destructs def agent fds = do
  if null fds
    then Right def
    else case destructs of
      [] ->
        let (states, checks) = analyzePhase2States description (map fst fds)
        in constructIfsTemp checks (states `zip` map snd fds)
      -- TODO: [Multiple branches] We currently find groups of projections.
      -- if we have receipts for the same recipe and frame key and then those will create
      -- duplicate let statements.
      -- We need to not have a name based left hand term in those cases
      -- Additionally, the checks could be compressed/deduped
      [r] : receiptGroups -> do
        (dTerm, positiveFDs, negativeFDs) <- getPositiveAndNegativeFDs r
        let recCall = constructReceiveTryCatch description constructIfsTemp receiptGroups def agent
        if null positiveFDs
          then do
            recCall negativeFDs
          else do
            tryTrue <- recCall positiveFDs
            tryFalse <- recCall negativeFDs
            let nameBased = toNameBasedSTerm (fst (head positiveFDs)) (TVariable (frameKey r))
            return (SLet (PTerm nameBased) (toNameBasedSTerm (fst (head positiveFDs)) dTerm) tryTrue tryFalse)
      (r:rest) : receiptGroups -> do
        (dTerm, positiveFDs, negativeFDs) <- getPositiveAndNegativeFDs r
        
        -- enrich positive and neg with rest of checks
        let updatedPositiveFDs = applySquashedProjectionChecksToFrames description positiveFDs (r:rest)
        let updatedNegativeFDs = applySquashedProjectionChecksToFrames description negativeFDs (r:rest)
        
        let recCall = constructReceiveTryCatch description constructIfsTemp receiptGroups def agent

        if null updatedPositiveFDs
          then do
            tryFalse <- recCall negativeFDs
            return (SLet (PVar (frameKey r)) dTerm SNil tryFalse)
          else do
            tryTrue <- recCall updatedPositiveFDs
            tryFalse <- recCall updatedNegativeFDs
            let firstPositiveFDFrame = fst (head updatedPositiveFDs)
            return (translateToSquashedProjectionGroup firstPositiveFDFrame (r:rest) tryTrue tryFalse)
    where
      getPositiveAndNegativeFDs :: RewriteReceipt -> Either SapicTranslationError (STerm, [(SFrame, Choreography)], [(SFrame, Choreography)])
      getPositiveAndNegativeFDs r =
        let l = frameKey r
            destructor = ruleFunction r
            ruleMapping = ruleArgsToRecipeMap r
            constrRecipe = subjectRecipe r
            dTerm = constructT description destructor ruleMapping (TVariable constrRecipe)
        in do
          -- We need to split frame in groups depending on receipts being
          -- reproducible
            (positiveFDs, negativeFDs) <-
              partitionFrames
                description
                agent
                dTerm
                (TVariable l)
                fds
            return (dTerm, positiveFDs, negativeFDs)

---
applySquashedProjectionChecksToFrames :: ProtocolDescription -> [(SFrame, Choreography)] -> [RewriteReceipt] -> [(SFrame, Choreography)]
applySquashedProjectionChecksToFrames description fds squashedReceipts =
  [ (applyAllReceipts frame squashedReceipts, choreo) | (frame, choreo) <- fds]
  where
    applyAllReceipts :: SFrame -> [RewriteReceipt] -> SFrame
    applyAllReceipts fr [] = fr
    applyAllReceipts fr (r:res) = 
      let updatedFrame = applySquashedReceiptToFrame description fr r
      in applyAllReceipts  updatedFrame res

applySquashedReceiptToFrame :: ProtocolDescription ->  SFrame -> RewriteReceipt -> SFrame
applySquashedReceiptToFrame description frame receipt = do
  let s = TVariable (frameKey receipt)
  let destructor = ruleFunction receipt
  let ruleMapping = ruleArgsToRecipeMap receipt
  let constrRecipe = subjectRecipe receipt
  let t = constructT description destructor ruleMapping (TVariable constrRecipe)
  let frame' = insertCheckAsTerms (s, t) frame
  tryMarkSquashedProjectionVariableAsBounded frame' (frameKey receipt)
---
--------- Construct the term from destructor rule fx. dcrypt(X1, scrypt(X1, X2, X3))
constructT :: ProtocolDescription -> Function -> [(RTerm, STerm)] -> STerm -> STerm
constructT description destructorSymbol recipeMap constructorTerm = do
  let rules = systemRules (getRewriteSystem description)
  let rule = fromJust (find (\r -> destructor r == destructorSymbol) rules)
  constructTermBasedOnRule rule recipeMap constructorTerm

constructTermBasedOnRule :: Rule -> [(RTerm, STerm)] -> STerm -> STerm
constructTermBasedOnRule rl recipeMap constructorTerm =
  let resolve rt = fromMaybe constructorTerm (lookup rt recipeMap)
      args'      = map resolve (args rl)
  in TFunction (destructor rl) args'
---------

partitionFrames :: ProtocolDescription -> Agent -> STerm -> STerm -> [(SFrame, Choreography)] ->
  Either SapicTranslationError ([(SFrame, Choreography)], [(SFrame, Choreography)])
partitionFrames description agent s t fds = do
  let checkFD (state, choreo) =
          let f = mapping state
              state' = insertCheckAsTerms (s, t) state
          in case (applyFrame description state s, applyFrame description state t) of
              (Right s', Right t') -> do
                if s' == t'
                  then Right (Left (state', choreo)) -- goes to positiveFDs
                  else Right (Right (state', choreo)) -- goes to negativeFDs
              (Left _, _) -> do
                Right (Right (state', choreo)) -- Left (FrameError err)
              (_, Left m) -> do
                Right (Right (state', choreo)) -- Left (FrameError err)
  partitionedFDs <- traverse checkFD fds
  return (Either.partitionEithers partitionedFDs)

constructReceiveIfs :: SapicTranslatorFunction -> ProtocolDescription -> SProcess -> Agent -> [Check] -> [(SFrame, Choreography)] -> Either SapicTranslationError SProcess
constructReceiveIfs mainTranslationFunction description def agent newChecks fds = 
  if null fds
  then Right def
  else case newChecks of
    [] -> mainTranslationFunction description agent fds
    (s, t) : newChecks' -> do
      let s' = recipeToTerm s
      let t' = recipeToTerm t
      (positiveFDs, negativeFDs) <- partitionFrames description agent s' t' fds
      let recCall = constructReceiveIfs mainTranslationFunction description def agent newChecks'
      ifTrue <- recCall positiveFDs
      ifFalse <- recCall negativeFDs
      
      let firstPositiveFDFrame = fst (head fds)
      let s'' = toNameBasedSTerm firstPositiveFDFrame s'
      let t'' = toNameBasedSTerm firstPositiveFDFrame t'
      return (SIf s'' t'' ifTrue ifFalse)

-- | Constructs a default behavior based on a list of default choreography clauses.
--
-- Returns
-- * 'Left' error if no valid default is found.
-- * 'Right' a default local behavior.
constructDefault :: SapicTranslatorFunction -> ProtocolDescription -> Agent -> [(SFrame, CDefault)] -> Either SapicTranslationError SProcess
constructDefault _ _ _ [] = Left "UndefinedError"
constructDefault _ _ _ fcdefs@((_, Epsilon) : _) = do
  _ <- constructDefaultEpsilon fcdefs
  Right SNil
constructDefault mainTranslationFunction description agent fcdefs@((_, Otherwise _) : _) = do
  fdefs <- constructDefaultOtherwise fcdefs
  mainTranslationFunction description agent fdefs

-- | Constructs a default behavior when all defaults are 'Epsilon'.
--
-- Returns
-- * 'Right' an empty list if successful.
-- * 'Left' error if any element is not 'Epsilon'.
constructDefaultEpsilon :: [(SFrame, CDefault)] -> Either SapicTranslationError [(SFrame, Choreography)]
constructDefaultEpsilon [] = return []
constructDefaultEpsilon ((_, Epsilon) : fcdefs) = do
  _ <- constructDefaultEpsilon fcdefs
  return []
constructDefaultEpsilon _ = Left "DifferentTypes default"

-- | Constructs a default behavior when all defaults are 'Otherwise'.
--
-- Returns
-- * 'Right' a list of frame-choreography pairs.
-- * 'Left' error if any element is not 'Otherwise'.
constructDefaultOtherwise :: [(SFrame, CDefault)] -> Either SapicTranslationError [(SFrame, Choreography)]
constructDefaultOtherwise [] = return []
constructDefaultOtherwise ((state, Otherwise c) : fcdefs) = do
  fcdefs' <- constructDefaultOtherwise fcdefs
  return ((state, c) : fcdefs')
constructDefaultOtherwise _ = Left "DifferentTypes default"