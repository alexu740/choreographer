module Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Condition where

import qualified Types.Rewrite as State
import Types.Choreography (Atomic (..), Term (..))
import Types.Simple (Cell)
import Types.LocalBehavior (Label)
import Types.Rewrite (TranslationResult, TranslationError(..))

-- | Extracts all 'If' substructure in a list of state-atomic pairs.
--
-- Returns
-- * 'Right' the list of extracted pairs if all checks pass.
-- * 'Left' error if any atomic is not a 'Read', or if there is no recipe.
extractIf :: [(State.State, Atomic)] -> TranslationResult [(State.State, Term, Term, Atomic, Atomic)]
extractIf [] = return []
extractIf ((state, If s t atomP atomN) : fas) = do
  fttaas <- extractIf fas
  return ((state, s, t, atomP, atomN) : fttaas)
extractIf _ = Left $ DifferentTypes "if"
