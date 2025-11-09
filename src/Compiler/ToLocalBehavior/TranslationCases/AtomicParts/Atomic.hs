module Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Atomic where

import Types.Choreography (Atomic (..),  Choreography (..))
import Types.LocalBehavior (LocalAtomic (..), LocalBehavior (..))

import qualified Choreography.Frame as Frame
import qualified Types.Rewrite as State

import Types.Rewrite as Description ( Description(constructors), FrameError(..), TranslationError(..), State (sessionID),TranslationResult )
import Types.Signatures (LocalBehaviorTranslatorFunction)

import qualified Data.List as List
import qualified Data.List.NonEmpty as ListNonEmpty

import Compiler.ToLocalBehavior.RecipeUtility (constructRecipe)
import Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Nonce (extractNonce)
import Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Read (extractRead)
import Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Write (extractWrite)
import Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Condition (extractIf)
import Compiler.ToLocalBehavior.TranslationCases.AtomicParts.PrivacyExtension
    ( translateMode, extractChoice, translateFormula, extractRelease )
import Compiler.ToLocalBehavior.TranslationCases.AtomicParts.Unlock (extractUnlock)


-- | Translates a list of state-atomic pairs for this locked agent.
--
-- Returns
-- * A atomic part for a local behavior.
translateAtomic :: LocalBehaviorTranslatorFunction -> Description -> [(State, Atomic)] -> TranslationResult LocalAtomic
translateAtomic _ _ [] = Left UndefinedError
translateAtomic translateWithDescription description fas@((state, atom) : _) =
  let constructors = Description.constructors description
      l = Frame.newLabel (map (State.frame . fst) fas)
  in case atom of
    Nonce {} -> do
      extractedFas <- extractNonce l fas
      translatedFas <- translateAtomic translateWithDescription description extractedFas
      return (LNew l translatedFas)
    Read _ cell _ _ -> do
      ftas <- extractRead l cell fas
      let (fts, fas') = unzip [((f, t), (f, a)) | (f, t, a) <- ftas]
      recipe <- constructRecipe constructors fts
      translatedFas <- translateAtomic translateWithDescription description fas'
      return (LRead l cell recipe translatedFas)
    Write cell _ _ _ -> do
      fttas <- extractWrite cell fas
      let (ft1s, ft2s, fas') =
              unzip3 [((f, t1), (f, t2), (f, a)) | (f, t1, t2, a) <- fttas]
      recipe1 <- constructRecipe constructors ft1s
      recipe2 <- constructRecipe constructors ft2s
      translatedFas <- translateAtomic translateWithDescription description fas'
      return (LWrite cell recipe1 recipe2 translatedFas)
    If {} -> do
      fttaas <- extractIf fas
      let (ft1s, ft2s, fa1s, fa2s) =
              List.unzip4 [((f, t1), (f, t2), (f, a1), (f, a2)) | (f, t1, t2, a1, a2) <- fttaas]
      recipe1 <- constructRecipe constructors ft1s
      recipe2 <- constructRecipe constructors ft2s
      fa1s' <- translateAtomic translateWithDescription description fa1s
      fa2s' <- translateAtomic translateWithDescription description fa2s
      return (LIf recipe1 recipe2 fa1s' fa2s')
    Choice mode _ dom _ -> do
      let mode' = translateMode mode
      extracted <- extractChoice l mode dom fas
      fas' <- translateAtomic translateWithDescription description extracted
      return (LChoice mode' l dom fas')
    Release mode formula _ -> do
      let mode' = translateMode mode
      formula' <- translateFormula constructors state formula -- TODO : check all frames give the same formula
      extracted <- extractRelease mode formula fas
      fas' <- translateAtomic translateWithDescription description extracted
      return (LRelease mode' formula' fas')
    Unlock _ -> do
      extracted <- extractUnlock fas
      fas' <- translateWithDescription description extracted
      return (LUnlock fas')
