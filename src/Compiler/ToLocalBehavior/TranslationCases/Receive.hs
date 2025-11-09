{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToLocalBehavior.TranslationCases.Receive where

import Types.Simple (  Cell, Constructors,  Mode (..), FUNCTIONS(..))
import Types.LocalBehavior (LocalAtomic (..),   LocalBehavior (..), Domain, Label, Recipe (..), Formula(..))
import Types.Choreography ( Agent, Term (..), Atomic (..),  Choreography (..))
import Types.Rewrite (FrameError(..), TranslationError(..), DestructorApp (..),  Checks, TranslationResult)
import Types.Signatures (LocalBehaviorTranslatorFunction)

import qualified Types.Rewrite as State
import qualified Types.Rewrite as Description
import qualified Types.Choreography as Choreography

import Compiler.ToLocalBehavior.CheckGenerator (analyzePhase2States)
import Compiler.ToLocalBehavior.TermRewriter (analyzePhase1States)
import Choreography.State (insertCheck, insertFrame)
import Choreography.Frame (newIndex, applyFrame)

import Debug.Trace (trace, traceM, traceShowId)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow, pPrint)

import qualified Data.Either as Either

-- | Translates a receive given the label, the receiving agent, and a list of frame-choreography pairs.
--
-- Returns
-- * 'Right' the resulting local behavior.
-- * 'Left' error if the extraction of receives fail.
translateReceive :: LocalBehaviorTranslatorFunction -> Label -> Description.Description -> [(State.State, Choreography)] -> TranslationResult LocalBehavior
translateReceive translateWithDescription l description fcs = do
  (fds, cdefs) <- extractReceive l (Description.agent description) fcs

  let agentName = Description.agent description
  let freshI = newIndex (map (State.frame . fst) fds)
  let (states, destructors) = analyzePhase1States freshI description (map fst fds)
  let fds1 = states `zip` map snd fds

  localDef <- constructDefault translateWithDescription description cdefs
  let constructIfsTemp = constructReceiveIfs translateWithDescription localDef description
  if null destructors
    then
      let (states', checks) = analyzePhase2States description states
          fds2 = states' `zip` map snd fds1
      in (
          if null checks
          then do
            fds3 <- translateWithDescription description fds2
            return (LReceive l fds3)
          else do
            fds3 <- constructIfsTemp checks fds1
            return (LReceive l $ LLock fds3)
        )
    else do
      fds2 <- constructReceiveTryCatch constructIfsTemp destructors localDef description fds1
      return (LReceive l $ LLock fds2)

-- | Extracts all receive-substructures for a 'Interaction' structure
--   given the new label, the receiving agent, and a list of frame-choreography pairs.
--
-- Returns
-- * 'Right' a list of frame-choreography pairs.
-- * 'Left' error if any atomic is not a 'Interaction', or the receive agents are different.
extractReceive :: Label -> Agent -> [(State.State, Choreography)] -> TranslationResult ([(State.State, Choreography)], [(State.State, Choreography.CDefault)])
extractReceive _ _ [] = return ([], [])
extractReceive l agent ((state, Interaction _ toAgent tcs cdef) : tail)
  | agent /= toAgent = Left $ DifferentAgents agent toAgent
  | otherwise = do
      let frames = map ((\t -> insertFrame l t state) . fst) tcs -- F^i_j = F_i[ l |-> t^i_j ]
      let fds = frames `zip` map snd tcs -- [..., (F^i_j, D^i_j), ...]

      (fcs', cdefs) <- extractReceive l agent tail

      return (fds ++ fcs', (state, cdef) : cdefs)
extractReceive _ _ _ = Left $ DifferentTypes "receive"


-- | Constructs all the try-catch checks to distinguish the receive choices.
-- Returns
-- * The resulting local atomic.
constructReceiveTryCatch :: (Checks -> [(State.State, Choreography)] -> TranslationResult LocalAtomic) -> [DestructorApp] -> LocalBehavior -> Description.Description -> [(State.State, Choreography)] -> TranslationResult LocalAtomic
constructReceiveTryCatch constructIfsTemp destructs def description fds =
  if null fds
    then Right $ LUnlock def
    else case destructs of
      [] ->
        let (states, checks) = analyzePhase2States description (map fst fds)
         in constructIfsTemp checks (states `zip` map snd fds)
      d : destructs' ->
        let l = dlabel d
            destructor = ddestructor d
            subterms = dsubterms d
         in do
              (positiveFDs, negativeFDs) <-
                partitionFrames
                  description
                  (LComp destructor subterms)
                  (LAtom l)
                  fds

              let recCall = constructReceiveTryCatch constructIfsTemp destructs' def description

              if null positiveFDs
                then recCall negativeFDs
                else do
                  tryTrue <- recCall positiveFDs
                  tryFalse <- recCall negativeFDs
                  return (LTry l destructor subterms tryTrue tryFalse)

-- | Constructs all the if-then-else checks to distinguish the receive choices.
--
-- Returns
-- * The resulting local atomic.
constructReceiveIfs :: LocalBehaviorTranslatorFunction -> LocalBehavior -> Description.Description -> Checks -> [(State.State, Choreography)] -> TranslationResult LocalAtomic
constructReceiveIfs translateWithDescription def description newChecks fds =
  if null fds
  then Right $ LUnlock def
  else case newChecks of
    [] -> do
      fds' <- translateWithDescription description fds
      return (LUnlock fds')
    (s, t) : newChecks' -> do
      (positiveFDs, negativeFDs) <- partitionFrames description s t fds
      let recCall = constructReceiveIfs translateWithDescription def description newChecks'
      ifTrue <- recCall positiveFDs
      ifFalse <- recCall negativeFDs
      return (LIf s t ifTrue ifFalse)

partitionFrames ::
  Description.Description ->
  Recipe ->
  Recipe ->
  [(State.State, Choreography)] ->
  Either TranslationError ([(State.State, Choreography)], [(State.State, Choreography)])
partitionFrames description s t fds = do
  let rwRules = Description.rewriteRules description
  let cs = Description.constructors description
  let checkFD (state, choreo) =
        let f = State.frame state
            state' = insertCheck (s, t) state
        in case (applyFrame rwRules cs f s, applyFrame rwRules cs f t) of
            (Right s', Right t') -> do
              if s' == t'
                then Right (Left (state', choreo)) -- goes to positiveFDs
                else Right (Right (state', choreo)) -- goes to negativeFDs
            (Left _, _) -> Right (Right (state', choreo)) -- Left (FrameError err)
            (_, Left _) -> Right (Right (state', choreo)) -- Left (FrameError err)
  partitionedFDs <- traverse checkFD fds
  return (Either.partitionEithers partitionedFDs)

-- | Constructs a default behavior based on a list of default choreography clauses.
--
-- Returns
-- * 'Left' error if no valid default is found.
-- * 'Right' a default local behavior.
constructDefault :: LocalBehaviorTranslatorFunction -> Description.Description -> [(State.State, Choreography.CDefault)] -> TranslationResult LocalBehavior
constructDefault _ _ [] = Left UndefinedError
constructDefault _ _ fcdefs@((_, Choreography.Epsilon) : _) = do
  _ <- constructDefaultEpsilon fcdefs
  Right LNil
constructDefault translateWithDescription description fcdefs@((_, Choreography.Otherwise _) : _) = do
  fdefs <- constructDefaultOtherwise fcdefs
  translateWithDescription description fdefs

-- | Constructs a default behavior when all defaults are 'Epsilon'.
--
-- Returns
-- * 'Right' an empty list if successful.
-- * 'Left' error if any element is not 'Epsilon'.
constructDefaultEpsilon :: [(State.State, Choreography.CDefault)] -> TranslationResult [(State.State, Choreography)]
constructDefaultEpsilon [] = return []
constructDefaultEpsilon ((_, Choreography.Epsilon) : fcdefs) = do
  _ <- constructDefaultEpsilon fcdefs
  return []
constructDefaultEpsilon _ = Left $ DifferentTypes "default"

-- | Constructs a default behavior when all defaults are 'Otherwise'.
--
-- Returns
-- * 'Right' a list of frame-choreography pairs.
-- * 'Left' error if any element is not 'Otherwise'.
constructDefaultOtherwise :: [(State.State, Choreography.CDefault)] -> TranslationResult [(State.State, Choreography)]
constructDefaultOtherwise [] = return []
constructDefaultOtherwise ((state, Choreography.Otherwise c) : fcdefs) = do
  fcdefs' <- constructDefaultOtherwise fcdefs
  return ((state, c) : fcdefs')
constructDefaultOtherwise _ = Left $ DifferentTypes "default"