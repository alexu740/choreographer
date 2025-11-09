{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Nonce where

import qualified Types.Rewrite as State
import Types.Choreography (Atomic (..), Term (..))
import Types.LocalBehavior (Label)
import Choreography.State (insertFrame)
import Types.Rewrite (TranslationError(..), TranslationResult)

-- | Extracts all 'Nonce' substructures in a list of state-atomic pairs.
--
-- Returns
-- * 'Right' the list of extracted pairs if all checks pass.
-- * 'Left' error if any atomic is not a 'Nonce'.
extractNonce :: Label -> [(State.State, Atomic)] -> TranslationResult [(State.State, Atomic)]
extractNonce _ [] = return []
extractNonce l ((state, Nonce var atom) : fas) = do
  fas' <- extractNonce l fas
  let state' = insertFrame l (Atomic var) state
  return ((state', atom) : fas')
extractNonce _ _ = Left $ DifferentTypes "nonce"
