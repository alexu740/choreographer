{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToLocalBehavior.TranslationCases.AtomicParts.PrivacyExtension where

import Types.Simple (Constructors,  Mode (..))
import qualified Types.Rewrite as State
import qualified Types.Choreography as C
import qualified Types.LocalBehavior as LBT
import Types.Choreography (Atomic (..),  Choreography (..), Term (..), Formula(..))
import Types.LocalBehavior ( Label, Domain, Recipe (..))
import Types.Rewrite (TranslationResult, TranslationError(..))
import Compiler.ToLocalBehavior.RecipeUtility (compose)
import Choreography.State (insertFrame)

-- | Translates a choreography mode to a local behavior mode.
translateMode :: Mode -> Mode
translateMode mode =
  case mode of
    Star -> Star
    Diamond -> Diamond

-- | Translates a 'Choice' substructure in a list of state-atomic pairs.
--
-- Returns
-- * 'Right' the list of extracted pairs if all checks pass.
-- * 'Left' error if any atomic is not a 'Choice', or if any mode/domain mismatch occurs.
extractChoice :: Label -> Mode -> Domain -> [(State.State, Atomic)] -> TranslationResult [(State.State, Atomic)]
extractChoice _ _ _ [] = return []
extractChoice l mode dom ((state, Choice mode' var dom' atom') : fas)
  | mode /= mode' = Left $ DifferentTypes "mode"
  | dom /= dom' = Left $ DifferentTypes "domain"
  | otherwise = do
      fas' <- extractChoice l mode dom fas
      let state' = insertFrame l (Atomic var) state
      return ((state', atom') : fas')
extractChoice _ _ _ _ = Left $ DifferentTypes "choice"


-- | Translates a choreography formula to a local behavior formula.
translateFormula :: Constructors -> State.State -> C.Formula -> TranslationResult LBT.Formula
translateFormula constructors state formula = case formula of
  Top -> return LBT.Top
  Equality t1 t2 ->
    case (compose constructors state t1, compose constructors state t2) of
      (Just r1, Just r2) -> return (LBT.Equality r1 r2)
      (Nothing, _) -> Left . NoRecipe $ [(frame, t1)]
      (_, Nothing) -> Left . NoRecipe $ [(frame, t2)]
  Neg f -> do
    f' <- translateFormula constructors state f
    return (LBT.Neg f')
  And f1 f2 -> do
    f1' <- translateFormula constructors state f1
    f2' <- translateFormula constructors state f2
    return (LBT.And f1' f2')
  where
    frame = State.frame state

-- | Translates a 'Release' substructure in a list of state-atomic pairs.
--
-- Returns
-- * 'Right' the list of extracted pairs if all checks pass.
-- * 'Left' error, if any atomic is not a 'Release', or if any mode/formula mismatch occurs.
extractRelease :: Mode -> Formula -> [(State.State, Atomic)] -> TranslationResult [(State.State, Atomic)]
extractRelease _ _ [] = return []
extractRelease mode formula ((state, Release mode' formula' atom') : fas)
  | mode /= mode' = Left $ DifferentTypes "release-modes"
  | formula /= formula' = Left $ DifferentTypes "release-formulas"
  | otherwise = do
      fas' <- extractRelease mode formula fas
      return ((state, atom') : fas')
extractRelease _ _ _ = Left $ DifferentTypes "release"
