{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.TranslationCases.AtomicCases where

import Compiler.ToSapicPlus.SFrame (SFrame, insertTermsInFrame, getLatestFrameKey, insertTermInFrameWithReturn, insertBoundedEntry)
import Types.Choreography (Agent, Atomic(..), Choreography(..), Term(..), Variable)
import Types.Sapic (SProcess(..), SapicTranslationError, SVariable, STerm(..))
import Types.Signatures (SapicTranslatorFunction)
import Compiler.ToSapicPlus.RecipeUtility (constructCommmonRecipe, recipeToTerm)
import Types.Simple ( Cell, FUNCTIONS(CELL))
import Types.ChoreographyProtocolShell (ProtocolDescription)

translateAtomic :: SapicTranslatorFunction -> ProtocolDescription -> Agent -> [(SFrame, Atomic)] -> Either SapicTranslationError SProcess
translateAtomic _ _ _ [] = Left "UndefinedError"
translateAtomic mainTranslateFunction description agent pairs@((state, atom) : _) =
--  let constructors = Description.constructors description
    case atom of
    Nonce {} -> do
      if all (isNewNonceStep . snd) pairs
      then do
        let (firstVar : rest) = extractNonceVars pairs
        if all (== firstVar) rest
        then do
          let nextPairs = map updatePair pairs
          furtherTranslation <- translateAtomic mainTranslateFunction description agent nextPairs
          return (SNew (TName firstVar) furtherTranslation)
        else Left "DifferentVariables nonce"
      else Left "DifferentTypes nonce"
    Read _ cell _ _ -> do
      ftas <- extractRead cell pairs
      let (_, _, _, newVar) = head ftas
      let (fts, fas') = unzip [((f, t), (f, a)) | (f, t, a, _) <- ftas]
      recipe <- constructCommmonRecipe description fts
      translatedFas <- translateAtomic mainTranslateFunction description agent fas'
      return (SLookup (recipeToTerm recipe) newVar translatedFas SNil)
    Write cell _ _ _ -> do
      fttas <- extractWrite cell pairs
      let (ft1s, ft2s, fas') = unzip3 [((f, t1), (f, t2), (f, a)) | (f, t1, t2, a) <- fttas]
      recipe1 <- constructCommmonRecipe description ft1s
      recipe2 <- constructCommmonRecipe description ft2s
      translatedFas <- translateAtomic mainTranslateFunction description agent fas'
      return (SInsert (recipeToTerm recipe1) (recipeToTerm recipe2) translatedFas)
    If {} -> do
      if all (isConditionStep . snd) pairs
        then do
          recipe1 <- constructCommmonRecipe description (map (getIfTerms "AllLeftTermsWithRespectiveFrames") pairs)
          recipe2 <- constructCommmonRecipe description (map (getIfTerms "AllRightTermsWithRespectiveFrames") pairs)
          fa1s' <- translateAtomic mainTranslateFunction description agent (map (getIfNextPairs "AllLeftNextPairs") pairs)
          fa2s' <- translateAtomic mainTranslateFunction description agent (map (getIfNextPairs "AllRightNextPairs") pairs)
          return (SIf (recipeToTerm recipe1) (recipeToTerm recipe2) fa1s' fa2s')
        else Left "DifferentTypes if"
    Unlock _ -> do 
      if all (isUnlockStep . snd) pairs
      then do
        let nextSteps = map extractUnlockNextChoreography pairs
        mainTranslateFunction description agent nextSteps
      else Left "DifferentTypes unlock"

isNewNonceStep :: Atomic -> Bool
isNewNonceStep (Nonce var atom) = True
isNewNonceStep _ = False

isConditionStep :: Atomic -> Bool
isConditionStep (If s t atomP atomN) = True 
isConditionStep _ = False

isUnlockStep :: Atomic -> Bool
isUnlockStep (Unlock choreo) = True
isUnlockStep _ = False

extractNonceVars :: [(SFrame, Atomic)] -> [Variable]
extractNonceVars pairs = [v | (_, Nonce v _) <- pairs]

updatePair :: (SFrame, Atomic) -> (SFrame, Atomic)
updatePair (frame, Nonce variable nextAtomic) =
  let (frame', newKey) = insertTermInFrameWithReturn frame (Atomic variable)
      frame'' = insertBoundedEntry frame' newKey
  in (frame'', nextAtomic)

extractUnlockNextChoreography :: (SFrame, Atomic) -> (SFrame, Choreography)
extractUnlockNextChoreography (state, Unlock choreo) = (state, choreo)

getIfTerms :: String -> (SFrame, Atomic) -> (SFrame, Term)
getIfTerms "AllLeftTermsWithRespectiveFrames" (frame, If s _ _ _) = (frame, s)
getIfTerms "AllRightTermsWithRespectiveFrames" (frame, If _ t _ _) = (frame, t)

getIfNextPairs :: String -> (SFrame, Atomic) -> (SFrame, Atomic)
getIfNextPairs "AllLeftNextPairs" (frame, If _ _ atomP _) = (frame, atomP)
getIfNextPairs "AllRightNextPairs" (frame, If _ _ _ atomN) = (frame, atomN)

extractWrite :: Cell -> [(SFrame, Atomic)] -> Either SapicTranslationError [(SFrame, Term, Term, Atomic)]
extractWrite _ [] = return []
extractWrite cell ((state, Write cell' term1 term2 atom) : fas)
  | cell /= cell' = Left "DifferentTypes cell"
  | otherwise = do
      fttas <- extractWrite cell fas
      return ((state, Composed CELL [Atomic cell, term1], term2, atom) : fttas)
extractWrite _ _ = Left "DifferentTypes write"

extractRead :: Cell -> [(SFrame, Atomic)] -> Either SapicTranslationError [(SFrame, Term, Atomic, SVariable)]
extractRead _ [] = return []
extractRead cell ((frame, Read var cell' term atom) : fas)
  | cell /= cell' = Left "DifferentTypes cell"
  | otherwise = do
      ftas <- extractRead cell fas
      let (frame', newVar) = insertTermInFrameWithReturn frame (Atomic var)
      return ((frame', Composed CELL [Atomic cell, term], atom, newVar) : ftas)
extractRead _ _ = Left "DifferentTypes read"
