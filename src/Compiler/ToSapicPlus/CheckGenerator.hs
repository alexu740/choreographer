{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.CheckGenerator where

import Types.Simple (FUNCTIONS(..))
import Types.Sapic ( Check, STerm, SVariable, SRecipe(..) )  
import Types.Choreography (Term(..))

import Compiler.ToSapicPlus.SFrame ( SFrame(..), insertChecks )
import Compiler.ToSapicPlus.RecipeUtility ( compose, composeSet )
import Compiler.ToSapicPlus.RewriteSystem.RewriteSystem (RewriteSystem(..), getRewriteSystem)


import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Types.ChoreographyProtocolShell (ProtocolDescription)
import Debug.Trace (trace, traceM, traceShowId)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)

-- checks will be used to sort frames into those that can or not satisfy the check, 
-- thus making an if-else chain
analyzePhase2States :: ProtocolDescription -> [SFrame] -> ([SFrame], [Check])
analyzePhase2States description states = 
  let (states', checks) = unzip $ map (analyzePhase2State description) states
      combinedChecks = combineChecks checks
  in (states', combinedChecks)


-- | Analyze a single state in Phase 2.
--   * Generates checks for compositional equivalences and key matches.
--   * Returns the updated checks and 
analyzePhase2State :: ProtocolDescription -> SFrame -> (SFrame, [Check])
analyzePhase2State description frame =
  -- non destructed labels are used, as destructed ones are already handled with let statements
  let nonDestructedLabels = Set.toList $ Map.keysSet (mapping frame) `Set.difference` Set.fromList (deconstructed frame)
      checks = analysisPhase2 description frame nonDestructedLabels
      verifierChecks = analysisPhase2Verify description frame (deconstructed frame)
      multChecks = analysisPhase2Mult description frame nonDestructedLabels
      exp1Checks = analysisPhase2Exp1 description frame nonDestructedLabels
      exp2Checks = analysisPhase2Exp2 description frame nonDestructedLabels
      -- Remove checks where both terms are in the initial knowledge
      checksOnInitialKnowledge = getChecksOnInitialKnowledge frame checks
      newChecks = (verifierChecks ++ checks ++ multChecks ++ exp1Checks ++ exp2Checks) `checkDifference` prevChecks frame `checkDifference` checksOnInitialKnowledge
      frame' = insertChecks newChecks frame
  in (frame', newChecks)

--------------------------------------------------------------------------------
-- Phase 2: Generate Checks
--------------------------------------------------------------------------------
analysisPhase2Verify :: ProtocolDescription -> SFrame -> [SVariable] -> [Check]
analysisPhase2Verify _ _ [] = []
analysisPhase2Verify description frame (xi : xs) =
  case Map.lookup xi (mapping frame) of
    Nothing -> [] -- will never reach here
    Just t ->
      let checkKey = keyCheck description xi frame t -- 
       in checkKey ++ analysisPhase2Verify description frame xs

-- | Phase 2: For each term in the frame, generate additional checks:
--   * Check for compositional equivalences.
--   * Check that keys match expected pairings.
analysisPhase2 :: ProtocolDescription -> SFrame -> [SVariable] -> [Check]
analysisPhase2 _ _ [] = []
analysisPhase2 description frame (xi : xs) =
  case Map.lookup xi (mapping frame) of
    Nothing -> [] -- will never reach here
    Just t ->
      let checkKey = keyCheck description xi frame t -- 
          checkSimilar = similarChecks description frame t
          checksAcc = checkKey ++ checkSimilar
       in checksAcc ++ analysisPhase2 description frame xs

-- | Generate checks for terms that are composable in multiple ways.
similarChecks :: ProtocolDescription -> SFrame -> Term -> [Check]
similarChecks description frame term =
  if isOperator term then []
  else 
    let constructors = systemConstructors (getRewriteSystem description)
    in case Set.toList (composeSet constructors frame term) of
      [] -> []
      x : xs -> map (x,) xs
  where 
    isOperator :: Term -> Bool
    isOperator (Composed MULT _) = True
    isOperator (Composed EXP _) = True
    isOperator _ = False

-- | Generate key-matching checks for decryption operations.
--  For example, if analyzing INV(k), ensure CRYPT(k, ...) decrypts appropriately.
keyCheck :: ProtocolDescription -> SVariable -> SFrame -> Term -> [Check]
keyCheck description xi frame term =
  case term of
    Composed REVEALSIGN [m, k] -> do
      case compose description frame m of
          Nothing -> []
          Just m' -> 
            case compose description frame (Composed PK [k]) of
              Nothing -> []
              Just k' -> 
                [(RFunction REVEALVERIFY [RVariable xi, m', k'], RFunction (UnDef "true") [])]
    Composed SIGN [m, k] -> do
      case compose description frame m of
          Nothing -> []
          Just m' -> 
            case compose description frame (Composed PK [k]) of
              Nothing -> []
              Just k' -> 
                [(RFunction VERIFY [RVariable xi, m', k'], RFunction (UnDef "true") [])]
    _ -> []

------
analysisPhase2Mult :: ProtocolDescription -> SFrame -> [SVariable] -> [Check]
analysisPhase2Mult description frame frameKeys = do
  let multTerms = [(key, terms) | (key, t1, t2) <- multTriples, terms <- [flattenMult t1 ++ flattenMult t2]]
  let pairsToCheck = pairs multTerms

  [check | Just check <- map mkCheck pairsToCheck]
  where
    multTriples :: [(SVariable, Term, Term)]
    multTriples =
      [ (key, a, b)
      | key <- frameKeys
      , Just (Composed MULT [a, b]) <- [Map.lookup key (mapping frame)]
      ]

    flattenMult :: Term -> [Term]
    flattenMult (Composed MULT [a, b]) = flattenMult a ++ flattenMult b
    flattenMult x@(Atomic t) = [x]
    flattenMult x@(Composed f args) = [x]

    pairs :: [a] -> [(a, a)]
    pairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]
      where
        tails [] = []
        tails l@(_:xs) = l : tails xs

    mkCheck :: ((SVariable, [Term]), (SVariable, [Term])) -> Maybe Check
    mkCheck ((xi, t1tn), (xj, s1sn)) = 
      let (td_terms, sd_terms) = shorten t1tn s1sn
      in case (td_terms, sd_terms) of
        ([], []) -> Nothing
        (td, sd) -> do
          let td' = nestMultLeft td
          let sd' = nestMultLeft sd
          let ltd = compose description frame td'
          let std = compose description frame sd'
          case ltd of
            Just foundLTD -> 
              case std of
                Just foundSTD -> 
                  Just (RFunction MULT [foundLTD, RVariable xj], RFunction MULT [foundSTD, RVariable xi])
                Nothing -> Nothing
            Nothing -> Nothing  

    binMult :: Term -> Term -> Term
    binMult a b = Composed MULT [a, b]

    nestMultLeft :: [Term] -> Term
    nestMultLeft (x:xs) = foldl binMult x xs
   
shorten :: [Term] -> [Term] -> ([Term], [Term])
shorten t s = (diffOnce t s, diffOnce s t)
  where 
    diffOnce :: Eq a => [a] -> [a] -> [a]
    diffOnce = foldl (flip List.delete)
    
---------------------------------
analysisPhase2Exp1 :: ProtocolDescription -> SFrame -> [SVariable] -> [Check]
analysisPhase2Exp1 description frame frameKeys = do
  let multTerms = [(key, a, terms) | (key, a, t2) <- expTriples, terms <- [flattenMult t2]]
  let pairsToCheck = pairs multTerms
  let relevantPairs = [((xi, terms1), (xj, terms2)) | p@((xi, a1, terms1), (xj, a2, terms2)) <- pairsToCheck, a1 == a2]
  [check | Just check <- map mkCheck relevantPairs]
  where
    expTriples :: [(SVariable, Term, Term)]
    expTriples =
      [ (key, a, b)
      | key <- frameKeys
      , Just (Composed EXP [a, b]) <- [Map.lookup key (mapping frame)]
      , not (isMult a)
      , isMult b
      ]

    flattenMult :: Term -> [Term]
    flattenMult (Composed MULT [a, b]) = flattenMult a ++ flattenMult b
    flattenMult x@(Atomic t) = [x]
    flattenMult x@(Composed f args) = [x]

    isMult :: Term -> Bool
    isMult (Composed MULT _) = True
    isMult _ = False

    pairs :: [a] -> [(a, a)]
    pairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]
      where
        tails [] = []
        tails l@(_:xs) = l : tails xs

    mkCheck :: ((SVariable, [Term]), (SVariable, [Term])) -> Maybe Check
    mkCheck ((xi, t1tn), (xj, s1sn)) = 
      let (td_terms, sd_terms) = shorten t1tn s1sn
      in case (td_terms, sd_terms) of
        ([], []) -> Nothing
        (td, sd) -> do
          let td' = nestMultLeft td
          let sd' = nestMultLeft sd
          let ltd = compose description frame td'
          let lsd = compose description frame sd'
          case ltd of
            Just foundLTD -> 
              case lsd of
                Just foundLSD -> 
                  Just (RFunction EXP [RVariable xj, foundLTD], RFunction EXP [RVariable xi, foundLSD])
                Nothing -> Nothing
            Nothing -> Nothing  

    binMult :: Term -> Term -> Term
    binMult a b = Composed MULT [a, b]

    nestMultLeft :: [Term] -> Term
    nestMultLeft (x:xs) = foldl binMult x xs
------------------------------------

analysisPhase2Exp2 :: ProtocolDescription -> SFrame -> [SVariable] -> [Check]
analysisPhase2Exp2 description frame frameKeys = do
  let multTerms = [(key, terms) | (key, t1, t2) <- multTriples, terms <- [flattenMult t1 ++ flattenMult t2]]
  let expTerms = [(key, a, terms) | (key, a, t2) <- expTriples, terms <- [flattenMult t2]]

  let pairsToCheck = [(e, m) | e <- expTerms, m <- multTerms]
  [check | Just check <- map mkCheck pairsToCheck]
  where
    expTriples :: [(SVariable, Term, Term)]
    expTriples =
      [ (key, a, b)
      | key <- frameKeys
      , Just (Composed EXP [a, b]) <- [Map.lookup key (mapping frame)]
      , not (isMult a)
      , isMult b
      ]

    multTriples :: [(SVariable, Term, Term)]
    multTriples =
      [ (key, a, b)
      | key <- frameKeys
      , Just (Composed MULT [a, b]) <- [Map.lookup key (mapping frame)]
      ]

    flattenMult :: Term -> [Term]
    flattenMult (Composed MULT [a, b]) = flattenMult a ++ flattenMult b
    flattenMult x@(Atomic t) = [x]
    flattenMult x@(Composed f args) = [x]

    isMult :: Term -> Bool
    isMult (Composed MULT _) = True
    isMult _ = False

    mkCheck :: ((SVariable, Term, [Term]), (SVariable, [Term])) -> Maybe Check
    mkCheck ((xi, a, t1tn), (xj, s1sn)) = 
      let (td_terms, sd_terms) = traceShowId(shorten t1tn s1sn)
      in case (td_terms, sd_terms) of
        ([], []) -> Nothing
        (_, []) -> Nothing
        ([], _) -> Nothing
        (td, sd) -> do
          let td' = nestMultLeft td
          let sd' = nestMultLeft sd
          let lA = compose description frame a
          let ltd = compose description frame td'
          let lsd = compose description frame sd'
          case ltd of
            Just foundLTD -> 
              case lsd of
                Just foundLSD -> 
                    case lA of
                      Just foundLA -> 
                        Just (RFunction EXP [foundLA, RFunction MULT [RVariable xj, foundLTD]], RFunction EXP [RVariable xi, foundLSD])
                      Nothing -> Nothing
                Nothing -> Nothing
            Nothing -> Nothing

    binMult :: Term -> Term -> Term
    binMult a b = Composed MULT [a, b]

    nestMultLeft :: [Term] -> Term
    nestMultLeft (x:xs) = foldl binMult x xs
--------------------------------------------------------------------------------
-- Utils
--------------------------------------------------------------------------------
getChecksOnInitialKnowledge :: SFrame -> [Check] -> [Check]
getChecksOnInitialKnowledge frame [] = []
getChecksOnInitialKnowledge frame ((t,s):rest) = 
  let subresult = getChecksOnInitialKnowledge frame rest
  in 
    if 
      isRecipeBasedOnInitialKnowledge frame t &&
      isRecipeBasedOnInitialKnowledge frame s
    then (t, s) : subresult
    else subresult

isRecipeBasedOnInitialKnowledge :: SFrame -> SRecipe -> Bool
isRecipeBasedOnInitialKnowledge frame recipe = 
  case recipe of
    RVariable v -> v `elem` initial frame
    RFunction f args -> all (isRecipeBasedOnInitialKnowledge frame) args

combineChecks :: [[Check]] -> [Check]
combineChecks = removeDuplicateChecks . concat

removeDuplicateChecks :: [Check] -> [Check]
removeDuplicateChecks = go Set.empty
  where
    go _ [] = []
    go seen ((a, b) : ls)
      | Set.member (a, b) seen || Set.member (b, a) seen = go seen ls
      | otherwise = (a, b) : go (Set.insert (a, b) seen) ls

checkDifference :: [Check] -> [Check] -> [Check]
checkDifference allChecks prevChecks =
  let prevChecksSet = Set.fromList prevChecks
  in go prevChecksSet allChecks
  where
    go _ [] = []
    go prev ((a, b) : ls)
      | Set.member (a, b) prev || Set.member (b, a) prev = go prev ls
      | otherwise = (a, b) : go prev ls
