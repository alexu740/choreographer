module Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Read where


import qualified Types.Rewrite as State
import Types.Choreography (Atomic (..), Term (..))
import Types.Simple (Cell)
import Types.LocalBehavior (Label)
import Choreography.State (insertFrame)
import Types.Rewrite (TranslationResult, TranslationError(..))

-- | Extracts all 'Read' substructure in a list of state-atomic pairs.
--
-- Returns
-- * 'Right' the list of extracted pairs if all checks pass.
-- * 'Left' error if any atomic is not a 'Read', or if there is no recipe.
extractRead :: Label -> Cell -> [(State.State, Atomic)] -> TranslationResult [(State.State, Term, Atomic)]
extractRead _ _ [] = return []
extractRead l cell ((state, Read var cell' term atom) : fas)
  | cell /= cell' = Left $ DifferentTypes "cell"
  | otherwise = do
      ftas <- extractRead l cell fas
      let state' = insertFrame l (Atomic var) state
      return ((state', term, atom) : ftas)
extractRead _ _ _ = Left $ DifferentTypes "read"