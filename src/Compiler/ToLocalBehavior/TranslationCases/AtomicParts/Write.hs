module Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Write where

import qualified Types.Rewrite as State
import Types.Choreography (Atomic (..), Term (..))
import Types.Simple ( Cell)
import Types.LocalBehavior (Label)
import Types.Rewrite (TranslationError(..), TranslationResult)


-- | Extracts all 'Write' substructure in a list of state-atomic pairs.
--
-- Returns
-- * 'Right' the list of extracted pairs if all checks pass.
-- * 'Left' error if any atomic is not a 'Read', or if there is no recipe.
extractWrite :: Cell -> [(State.State, Atomic)] -> TranslationResult [(State.State, Term, Term, Atomic)]
extractWrite _ [] = return []
extractWrite cell ((state, Write cell' term1 term2 atom) : fas)
  | cell /= cell' = Left $ DifferentTypes "cell"
  | otherwise = do
      fttas <- extractWrite cell fas
      return ((state, term1, term2, atom) : fttas)
extractWrite _ _ = Left $ DifferentTypes "write"