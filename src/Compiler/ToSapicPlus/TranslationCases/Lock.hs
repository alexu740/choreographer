{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.TranslationCases.Lock where

import Compiler.ToSapicPlus.SFrame (SFrame)
import Types.Choreography (Agent, Atomic(..), Choreography(..))
import Types.Sapic (SProcess(..), SapicTranslationError)
import Types.Signatures (SapicTranslatorFunction)

import Compiler.ToSapicPlus.TranslationCases.AtomicCases (translateAtomic)

import Debug.Pretty.Simple (pTraceM, pTraceShowId)
import Text.Pretty.Simple (pShow, pPrint)
import Types.ChoreographyProtocolShell (ProtocolDescription)

translateLock :: SapicTranslatorFunction -> ProtocolDescription -> Agent -> Agent -> [(SFrame, Choreography)] -> Either SapicTranslationError SProcess
translateLock mainTranslateFunction description lockAgent targetAgent pairs = do
  if all (isLockStep . snd) pairs then do
    if all (isLockStepForAgent lockAgent . snd) pairs then do
      let nextPairs = map extractNextPairFromLock pairs
      if targetAgent == lockAgent
      then translateAtomic mainTranslateFunction description targetAgent nextPairs 
      else mainTranslateFunction description targetAgent (pruneAtomic nextPairs)
    else Left ("DifferentAgents from " <> lockAgent)
  else Left "DifferentTypes lock"

isLockStepForAgent :: Agent -> Choreography -> Bool
isLockStepForAgent agent (Lock lockAgent _) = agent == lockAgent
isLockStepForAgent _ _ = False

isLockStep :: Choreography -> Bool
isLockStep (Lock lockAgent _) = True
isLockStep _ = False

extractNextPairFromLock :: (SFrame, Choreography) -> (SFrame, Atomic)
extractNextPairFromLock (frame, Lock ag' nextAtomic) = (frame, nextAtomic)

-- | Translates a list of state-atomic pairs for another locked agent.
--
-- Returns
-- * The list of frames and next choreography, i.e. skips all atomic parts.
pruneAtomic :: [(SFrame, Atomic)] -> [(SFrame, Choreography)]
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