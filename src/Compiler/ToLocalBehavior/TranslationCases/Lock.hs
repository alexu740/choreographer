{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToLocalBehavior.TranslationCases.Lock where

import Types.Simple ( FUNCTIONS(..))
import Types.LocalBehavior (LocalBehavior (..))
import Types.Choreography (Agent, Term (..), Atomic (..))
import Types.Rewrite as Description ( Description(agent), FrameError(..), TranslationError(..), State (sessionID),TranslationResult )
import Types.Choreography as Choreography (Choreography(Lock))
import Types.Signatures (LocalBehaviorTranslatorFunction)

import Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Atomic (translateAtomic)
-- | Translates a lock given the lock-status, the locking agent, and a list of frame-choreography pairs.
--
-- Returns
-- * 'Right' the resulting local behavior.
-- * 'Left' error if the extraction of locks fail.
translateLock :: LocalBehaviorTranslatorFunction -> Agent -> Description.Description -> [(State, Choreography)] -> TranslationResult LocalBehavior
translateLock translateWithDescription lockAgent description fcs = do
  fas <- extractLock lockAgent fcs
  if Description.agent description == lockAgent
    then do
      fas' <- translateAtomic translateWithDescription description fas
      return (LLock fas')
    else translateWithDescription description (pruneAtomic fas)

-- | Extracts all lock-substructures in a list of frame-choreography pairs.
--
-- Returns
-- * 'Right' a list of state-atomic pairs.
-- * 'Left' error if the lock agent are different, or any block is not a lock.
extractLock :: Agent -> [(State, Choreography)] -> TranslationResult [(State, Atomic)]
extractLock _ [] = return []
extractLock agent ((frame, Lock ag' atom) : fcs)
  | agent /= ag' = Left $ DifferentAgents agent ag'
  | otherwise = do
      fcs' <- extractLock agent fcs
      return ((frame, atom) : fcs')
extractLock q m = Left $ DifferentTypes ("lock")

-- | Translates a list of state-atomic pairs for another locked agent.
--
-- Returns
-- * The list of frames and next choreography, i.e. skips all atomic parts.
pruneAtomic :: [(State, Atomic)] -> [(State, Choreography)]
pruneAtomic [] = []
pruneAtomic ((state, atom) : fas) =
  let recCall a = pruneAtomic ((state, a) : fas)
   in case atom of
        Nonce _ atom' -> recCall atom'
        Read _ _ _ atom' -> recCall atom'
        Write _ _ _ atom' -> recCall atom'
        If _ _ atom1 atom2 -> pruneAtomic ((state, atom1) : (state, atom2) : fas)
        Choice _ _ _ atom' -> recCall atom'
        Release _ _ atom' -> recCall atom'
        Unlock choreo -> (state, choreo) : pruneAtomic fas