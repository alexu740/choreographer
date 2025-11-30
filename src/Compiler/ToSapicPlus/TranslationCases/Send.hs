{-# LANGUAGE OverloadedStrings #-}


module Compiler.ToSapicPlus.TranslationCases.Send where

import Compiler.ToSapicPlus.SFrame (SFrame)
import Types.Choreography (Agent, Choreography(..), Term)
import Types.Sapic (SProcess(..), SapicTranslationError, SRecipe, STerm(..), SRecipe(..))
import Types.Signatures (SapicTranslatorFunction)

import Data.List as List
import qualified Data.Text as T

import Debug.Pretty.Simple (pTraceM, pTraceShowId)
import Text.Pretty.Simple (pShow, pPrint)

import Compiler.ToSapicPlus.RecipeUtility (constructCommmonRecipe, recipeToNameTerm)
import Compiler.ToSapicPlus.SecurityGoalUtility (applySecrecy)
import Types.ChoreographyProtocolShell (ProtocolDescription)

translateSend :: SapicTranslatorFunction -> ProtocolDescription -> Agent -> [(SFrame, Choreography)] -> Either SapicTranslationError SProcess
translateSend mainTranslationFunction description agent pairs = do
  let (Interaction _ _ tcs _) = snd (head pairs)
  let branchCount = length tcs
  framesTermsAndChoreos <- extractSend agent branchCount pairs -- choreos = [..., [D_1^i, ..., D_m^i], ...]

  (recipes, nextfcs) <- constructRecipesAndNextPairs description framesTermsAndChoreos
  let next = map (mainTranslationFunction description agent) nextfcs
  nextSeq <- sequence next
  let sTerms = map recipeToNameTerm recipes
  let termAndCorespondingProcessList = zip sTerms nextSeq
  if length termAndCorespondingProcessList == 1
    then return (SOut $ zip sTerms nextSeq)
    else 
     return $ SIn (TName "choice") (simulateNonDeterministicChoice 0 termAndCorespondingProcessList)
  where 
    --
    simulateNonDeterministicChoice :: Int -> [(STerm, SProcess)] -> SProcess
    simulateNonDeterministicChoice i [] = applySecrecy description agent (map fst pairs)
    simulateNonDeterministicChoice i ((t,c):r) = 
      SChoice (TName "choice") (T.pack (show i)) (SOut [(t,c)]) (simulateNonDeterministicChoice (i+1) r)
    --  

extractSend :: Agent -> Int -> [(SFrame, Choreography)] -> Either SapicTranslationError ([SFrame], [[Term]], [[Choreography]])
extractSend _ _ [] = return ([], [], [])
extractSend agent m ((frame, Interaction agentFrom _ tcs _) : fcs)
  | agent /= agentFrom = Left $ "DifferentAgents" <> agent <> agentFrom
  | length tcs /= m = Left "DifferentBranchLength"
  | otherwise =
      do
        (frames, terms, choreos) <- extractSend agent m fcs
        return (frame : frames, map fst tcs : terms, map snd tcs : choreos)
extractSend _ _ _ = Left "DifferentTypes send"


-- | Constructs all recipes with respect to the specification.
--   I.e. find all rj's such that for all i: Fi(rj) = t_j^i
--  Next choreography steps are also assembled according to specification
-- Input
-- * List of frames, i.e. [F1, ..., Fn]
-- * List of term-lists, i.e. [[t_1^1, ..., t_m1^1], ..., [t_1^n, ..., t_m^n]]
--
-- Returns
-- * 'Right' a list of recipes, if there is a uniform recipe for all frames and terms.
-- * 'Left' error, if any recipe construction fails.
constructRecipesAndNextPairs :: ProtocolDescription -> ([SFrame], [[Term]], [[Choreography]]) -> Either SapicTranslationError ([(SFrame, SRecipe)], [[(SFrame, Choreography)]])
constructRecipesAndNextPairs description (frames, branchTerms, nextChoreographies) =
  -- Group terms by branch index in their respective choreographies. Fx:
  -- C1 = Interaction _ _ [t1_1.D1_1, t1_2.D1_2]
  -- C2 = Interaction _ _ [t2_1.D1_2, t2_2.D2_2]
  -- The groups will be: [t1_1, t2_1] and [t1_2, t2_2]
  -- We need to also find a common recipe for each group, otherwise it is a ill defined spec
  let transposedTerms = List.transpose branchTerms -- [[t_1^1, ..., t_1^n], ..., [t_m^1, ..., t_mn^n]]
      transposedChoreos = List.transpose nextChoreographies -- [..., [D_j^1, ..., D_j^n], ...]

  -- Associate frame with terms. There must be m recipes, where m is the number of branches across
  -- all choreographies. The translation requires Fi(r_j) = t_i^j, where i < n, where n is the number of choreographies
  -- Fx. 
  -- F1(r1) = t1_1  F2(r1) = t2_1 <-- from group [t1_1, t2_1]
  -- F1(r2) = t1_2  F2(r2) = t2_2 <-- from group [t1_2, t2_2]
      fts = map (zip frames) transposedTerms -- [[(F1, t_1^1), ..., , (Fn, t_1^n)], ..., [(F1, t_m^1), ..., (Fn, t_mn^n)]]
      nextfcs = map (zip frames) transposedChoreos -- [..., [(F1, D_j^1), ..., (Fn, D_j^n)], ...]
  -- Each group (of branches) should yield one common recipe each
      recipesOrError = traverse (constructCommmonRecipe description) fts
      
  in case recipesOrError of
    Left m -> Left m
    Right recipes -> 
      let recipeWithFrameList = combine frames recipes
      in Right (recipeWithFrameList, nextfcs)

combine :: [a] -> [b] -> [(a,b)]
combine xs ys = [ (x,y) | x <- xs, y <- ys ]