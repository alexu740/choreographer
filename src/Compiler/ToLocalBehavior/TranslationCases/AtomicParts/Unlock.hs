module Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Unlock where

import qualified Types.Rewrite as State
import Types.Choreography (Atomic (..),  Choreography (..), Term (..))
import Types.Simple ( Cell)
import Types.LocalBehavior (Label)
import Types.Rewrite (TranslationError(..), TranslationResult)

-- | Translates a 'Unlock' structure in a list of state-atomic pairs.
--
-- Returns
-- * 'Right' a list of extracted pairs if all checks pass.
-- * 'Left' error, if any atomic is not a 'Unlock'.
extractUnlock :: [(State.State, Atomic)] -> TranslationResult [(State.State, Choreography)]
extractUnlock [] = return []
extractUnlock ((state, Unlock choreo) : fas) = do
  fas' <- extractUnlock fas
  return ((state, choreo) : fas')
extractUnlock _ = Left $ DifferentTypes "unlock"