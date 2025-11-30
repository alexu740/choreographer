{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.SyntacticSimplifier where

import Types.Choreography(Term(..), Choreography)
import Types.Sapic
    ( SPatternArg(..),
      SPattern(PData),
      SProcess(SIn, SOut, SInsert, SLookup, SLock, SUnlock, SNew, SNil,
               SIf, SLet, SChoice, SFact),
      STerm(TVariable, TName),
      SVariable,
      STerm(..),
      RTerm(..),
      Rule(args, result),
      SRecipe,
      SapicTranslationError )
import Compiler.ToSapicPlus.RecipeUtility (recipeToNameTerm, choreoTermToSTerm, h)

import Types.Simple (Function)
import Compiler.ToSapicPlus.SFrame(SFrame(..), toNameBasedSTerm, insertBoundedEntry)
import Compiler.ToSapicPlus.RewriteSystem.RewriteReceipt (RewriteReceipt(..))

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Text (Text)
import qualified Data.List as List
import Data.List (foldl', sortOn)

import Debug.Trace (trace, traceM, traceShowId)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)
------
-- Used in the receive step translation
-- Aggregates projection destructors in a block, which is to be processed together
------
resultVar :: Rule -> Maybe Text
resultVar rl = case result rl of
  RVar x -> Just x
  _ -> Nothing

getConstructor :: Rule -> Function -> Maybe [RTerm]
getConstructor rl f =
  case [ ps | RConstr g ps <- args rl, g == f ] of
    [ps] -> Just ps
    _ -> Nothing

indexOfResultInConstructorArgs :: Rule -> Function -> Maybe Int
indexOfResultInConstructorArgs rl f = do
  x  <- resultVar rl
  ps <- getConstructor rl f
  case [ i | (i, RVar y) <- zip [0..] ps, y == x ] of
    [i] -> Just i
    _ -> Nothing

subjectConstructor :: Term -> Function
subjectConstructor (Composed f _) = f

type ProjKey = (Function, Term)
aggregateReceiptsByContructorAndSubject :: [RewriteReceipt] -> [[RewriteReceipt]]
aggregateReceiptsByContructorAndSubject receipts = 
  let keyOf :: RewriteReceipt -> ProjKey
      keyOf r = let subj = subject r
                in (subjectConstructor subj, subj)
      buckets :: Map.Map ProjKey (Int, [RewriteReceipt])
      buckets =
        snd $ foldl' step (0 :: Int, Map.empty) receipts
        where
          step (!i, m) r =
            let k = keyOf r
            in case Map.lookup k m of
                 Nothing ->
                   (i + 1, Map.insert k (i, [r]) m)  -- first time the key occurs
                 Just (j, rs) ->
                   (i + 1, Map.insert k (j, rs ++ [r]) m)
  in map snd $ sortOn fst (Map.elems buckets)


translateToSquashedProjectionGroup :: SFrame -> [RewriteReceipt] -> SProcess -> SProcess -> SProcess
translateToSquashedProjectionGroup frame receipts@(r:rest) leftP rightP = do
  let constructorSymbol = subjectConstructor (subject r)
  let orderKey rr = maybe maxBound id (indexOfResultInConstructorArgs (rule rr) constructorSymbol)
  let receipts' = List.sortOn orderKey receipts

  let boundedVars = map (PBind . toNameBasedSTerm frame . TVariable . frameKey ) receipts'
  SLet (PData constructorSymbol boundedVars) (TVariable (subjectRecipe r)) leftP rightP

-------------
-------------


-- After the translation find blocks of let and ifs and try see if any "if" can be squashed in a let
-- V1. This is applied after the translation for a process is finished
compressIfBlocksOnSingularSyntacticBranch :: SProcess -> SProcess
compressIfBlocksOnSingularSyntacticBranch SNil = SNil
compressIfBlocksOnSingularSyntacticBranch (SIn x nextProc) = SIn x (compressIfBlocksOnSingularSyntacticBranch nextProc)
compressIfBlocksOnSingularSyntacticBranch (SOut pairs) = 
    SOut [ (x, compressIfBlocksOnSingularSyntacticBranch next) | (x, next) <- pairs ]
compressIfBlocksOnSingularSyntacticBranch (SInsert t1 t2 p) = SInsert t1 t2 (compressIfBlocksOnSingularSyntacticBranch p)
compressIfBlocksOnSingularSyntacticBranch (SLookup t1 t2 p1 p2) = 
    SLookup t1 t2 (compressIfBlocksOnSingularSyntacticBranch p1) (compressIfBlocksOnSingularSyntacticBranch p2)
compressIfBlocksOnSingularSyntacticBranch (SLock p) = SLock (compressIfBlocksOnSingularSyntacticBranch p)
compressIfBlocksOnSingularSyntacticBranch (SUnlock p) = SUnlock (compressIfBlocksOnSingularSyntacticBranch p)
compressIfBlocksOnSingularSyntacticBranch (SNew n p) = SNew n (compressIfBlocksOnSingularSyntacticBranch p)
compressIfBlocksOnSingularSyntacticBranch (SFact t args p) = SFact t args (compressIfBlocksOnSingularSyntacticBranch p)
compressIfBlocksOnSingularSyntacticBranch (SIf t1 t2 p1 p2) = 
  -- we don't care about random ifs, because those can't be squashed
  -- they are interesting only if in a linear block started with a Let
  SIf t1 t2 (compressIfBlocksOnSingularSyntacticBranch p1) (compressIfBlocksOnSingularSyntacticBranch p2)
compressIfBlocksOnSingularSyntacticBranch (SChoice t1 t2 p1 p2) = 
  SChoice t1 t2 (compressIfBlocksOnSingularSyntacticBranch p1) (compressIfBlocksOnSingularSyntacticBranch p2)
compressIfBlocksOnSingularSyntacticBranch start@(SLet sp t p1 p2) = do
  let block = findLinearBlock start
  case block of
    Nothing -> SLet sp t (compressIfBlocksOnSingularSyntacticBranch p1) (compressIfBlocksOnSingularSyntacticBranch p2)
    Just (parts, end) -> do
      let ifParts = [ p | p@(SIf {}) <- parts ]
      let letParts = [ p | p@(SLet {}) <- parts ]
      let (ifParts', letParts') = squashIfs ifParts letParts
      mergeBlock ifParts' letParts' end

mergeBlock :: [SProcess] -> [SProcess] -> SProcess -> SProcess
mergeBlock ifParts letParts endOfBlock = do
  let block = letParts ++ ifParts ++ [endOfBlock]
  createChain block
  
createChain :: [SProcess] -> SProcess
createChain [endOfBlock] = endOfBlock
createChain (first:rest) =
  case first of
    SLet pat scr pThen _ ->
      SLet pat scr (createChain rest) SNil
    SIf t1 t2 pThen _ ->
      SIf t1 t2 (createChain rest) SNil

squashIfs :: [SProcess] -> [SProcess] -> ([SProcess], [SProcess])
squashIfs ifParts letParts =
  foldl' step ([], letParts) ifParts
  where
    step :: ([SProcess], [SProcess]) -> SProcess -> ([SProcess], [SProcess])
    step (keptIfs, currentLets) ifp =
      case ifp of
        SIf t1 t2 p1 p2 ->
          let (didSquash, newLets) = squashOneIf t1 t2 currentLets
          in if didSquash
               then (keptIfs, newLets)
               else (keptIfs ++ [ifp], currentLets)
        _ -> (keptIfs ++ [ifp], currentLets)


findLinearBlock :: SProcess -> Maybe ([SProcess], SProcess)
findLinearBlock (SLet sp t p1 SNil) = do
  (blockParts, endOfBlock) <- findLinearBlock p1
  let updatedList = SLet sp t p1 SNil : blockParts
  Just (updatedList, endOfBlock)
findLinearBlock (SIf t1 t2 p1 SNil) = do
  (blockParts, endOfBlock) <- findLinearBlock p1
  let updatedList = SIf t1 t2 p1 SNil : blockParts
  Just (updatedList, endOfBlock)
findLinearBlock (SLet sp t p1 _) = Nothing
findLinearBlock (SIf t1 t2 p1 _) = Nothing
findLinearBlock p = Just ([], p)



-- Try to rewrite any SLet pattern args in the list by replacing a matching
-- PBind v (where t1 == TVariable v or t2 == TVariable v) with PCompare (the other term).
squashOneIf :: STerm -> STerm -> [SProcess] -> (Bool, [SProcess])
squashOneIf = mapAccumLOr update
  where
    mapAccumLOr :: (STerm -> STerm -> SProcess -> (Bool, SProcess))
                -> STerm -> STerm -> [SProcess]
                -> (Bool, [SProcess])
    mapAccumLOr f a b = go False
      where
        go changedSoFar [] = (changedSoFar, [])
        go changedSoFar (x:xs) =
          let (changedHere, x') = f a b x
              (changedTail, xs') = go (changedSoFar || changedHere) xs
          in (changedTail, x' : xs')

    update :: STerm -> STerm -> SProcess -> (Bool, SProcess)
    update a b (SLet (PData fun args) scr p1 p2) =
      let (changed, args') = replaceArgs a b args
      in (changed, SLet (PData fun args') scr p1 p2)
    update _ _ sp = (False, sp) -- other forms untouched

    -- Replace in pattern args: if we find PBind v where either a == TVariable v
    -- or b == TVariable v, switch that slot to PCompare.
    replaceArgs :: STerm -> STerm -> [SPatternArg] -> (Bool, [SPatternArg])
    replaceArgs a@(TVariable _) b@(TVariable _) args = go False args
      where
        go changed [] = (changed, [])
        go changed (arg:rest) =
          case arg of
            PBind v@(TVariable _)
              | a == v ->
                  let (ch2, rest') = go True rest
                  in (True, PCompare b : rest')
              | b == v ->
                  let (ch2, rest') = go True rest
                  in (True, PCompare a : rest')
              | otherwise ->
                  let (ch2, rest') = go changed rest
                  in (ch2, arg : rest')
            PCompare _ ->
              let (ch2, rest') = go changed rest
              in (ch2, arg : rest')
    replaceArgs _ _ args = (False, args)
    

---
receiveCaseSTermTranslation :: SFrame -> SVariable -> STerm
receiveCaseSTermTranslation frame var =
  let a = frame
  in case toNameBasedSTerm a (TVariable var) of
    TVariable x -> TVariable x
    TName n -> do
      let frameTerms = Map.elems (mapping frame)
      let occuranceOfName = length (filter (== Atomic n) frameTerms)
      if occuranceOfName == 1 
      then TName n
      else TVariable var
    

---
tryMarkSquashedProjectionVariableAsBounded :: SFrame -> SVariable -> SFrame
tryMarkSquashedProjectionVariableAsBounded frame term = 
  if shouldNewVariableBeBounded frame term
  then insertBoundedEntry frame term
  else frame

tryMarkIncomingVariableAsBounded :: [(SFrame, Choreography)] -> SVariable -> SFrame -> [(SFrame, Choreography)]
tryMarkIncomingVariableAsBounded fds addedVar firstFrame =
  if shouldNewVariableBeBounded firstFrame addedVar
  then 
    [ (insertBoundedEntry f addedVar, c) | (f,c) <- fds]
  else fds

shouldNewVariableBeBounded :: SFrame -> SVariable -> Bool
shouldNewVariableBeBounded frame var  =
  let term = Map.lookup var (mapping frame)
  in case term of
    Just (Atomic n) ->
      let frameTerms = Map.elems (mapping frame)
          occuranceOfName = length (filter (== Atomic n) frameTerms)
      in  occuranceOfName == 1
    _ -> False


recipeWithNameReplacement :: SRecipe -> [(SFrame, Term)] -> STerm
recipeWithNameReplacement recipe ((frame, _): rest) =
  recipeToNameTerm (frame, recipe)

variableWithNameReplacement :: SVariable -> [(SFrame, Term)] -> Either SapicTranslationError SVariable
variableWithNameReplacement term ((frame, _): rest) =
  variableToNameTerm (frame, term)
  
variableToNameTerm :: (SFrame, SVariable) -> Either SapicTranslationError SVariable
variableToNameTerm (frame, var) = do
  let sterm = choreoTermToSTerm $ mapping frame Map.! var
  case sterm of
    TName n -> Right n
    TVariable v -> Right v
    TFunction _ _ -> Left "Not allowed to read a cell into a composed term!"