{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.SFrame where

import Compiler.ToSapicPlus.RewriteSystem.RewriteReceipt (RewriteReceipt)

import Types.Simple (Function)
import Types.Sapic (Check, SVariable, STerm(..), SRecipe(..), SapicTranslationError, Rule, RTerm)
import Types.Choreography (Term(..))
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)

import Debug.Trace (trace, traceM, traceShowId, traceShow)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)


data SFrame = SFrame {
  mapping :: Map.Map SVariable Term,
  deconstructed :: [SVariable],
  bounded :: [SVariable],
  receipts :: [RewriteReceipt],
  prevChecks :: [Check],
  initial :: [SVariable]
} deriving(Eq, Show)

emptyFrame :: SFrame
emptyFrame = SFrame {
    mapping = Map.empty,
    deconstructed = [],
    bounded = [],
    receipts = [],
    prevChecks = [],
    initial = []
  }

-- TODO: Refactor logic for name based substitutions/bindings so it is in one place 
bindIfUnique :: SFrame -> SVariable -> Term -> SFrame
bindIfUnique frame key term@(Atomic t) = do
  let keysPointingToSameTerm = occurranceInFrame frame term
  if keysPointingToSameTerm == 1
  then
    insertBoundedEntry frame key
  else frame
bindIfUnique frame _ _ = frame

occurranceInFrame :: SFrame -> Term -> Int
occurranceInFrame frame term =
  length
    [ ()
    | v <- Map.elems (mapping frame)
    , v == term
    ]

initializeFrame :: [Term] -> SFrame
initializeFrame terms = 
  let frame' = insertTermsInFrame emptyFrame terms
      frame'' = frame' { bounded = Set.toList( Map.keysSet (mapping frame')) }
      frame''' = frame'' { initial = Set.toList( Map.keysSet (mapping frame'')) }
  in frame'''

insertCheckAsTerms :: (STerm, STerm) -> SFrame -> SFrame
insertCheckAsTerms (s,t) frame =
  frame {prevChecks = (sTermToSRecipe s, sTermToSRecipe t) : prevChecks frame}

sTermToSRecipe :: STerm -> SRecipe
sTermToSRecipe (TVariable v) = RVariable v
sTermToSRecipe (TFunction f ts) = RFunction f (map sTermToSRecipe ts)

insertCheck :: Check -> SFrame -> SFrame
insertCheck c frame =
  frame {prevChecks = c : prevChecks frame}

insertChecks :: [Check] -> SFrame -> SFrame
insertChecks cs frame =
  frame {prevChecks = cs ++ prevChecks frame}

insertReceipt :: SFrame -> RewriteReceipt -> SFrame
insertReceipt frame r =
  frame { receipts = r : receipts frame }

insertDeconstructedEntry :: SFrame -> SVariable -> SFrame
insertDeconstructedEntry frame key =
  frame { deconstructed = key : deconstructed frame }

insertBoundedEntry :: SFrame -> SVariable -> SFrame
insertBoundedEntry frame key =
  frame { bounded = key : bounded frame }

insertTermInFrameWithReturn :: SFrame -> Term -> (SFrame, SVariable)
insertTermInFrameWithReturn (SFrame mapping d b rs p i) term =
  let newIndex = Map.size mapping
      newKey = "X" <> T.pack (show newIndex)
      newMap = Map.insert newKey term mapping
  in (SFrame newMap d b rs p i, newKey)

insertTermInFrame :: SFrame -> Term -> SFrame
insertTermInFrame frame term = insertTermsInFrame frame [term]

insertTermsInFrame :: SFrame -> [Term] -> SFrame
insertTermsInFrame (SFrame mapping d b rs p  i) terms = SFrame updatedMapping d b rs p i
  where
    start = Map.size mapping
    updatedMapping = snd $ foldl step (start, mapping) terms
    step (i, acc) t =
      let k = T.pack ("X" ++ show i)
      in  (i + 1, Map.insert k t acc)

getLatestFrameKey :: SFrame -> Either T.Text SVariable
getLatestFrameKey (SFrame mp _ _ _ _ _)
  | Map.null mp = Left "EmptyFrame"
  | otherwise =
      let idx = Map.size mp - 1
          key = T.pack ("X" ++ show idx)
      in Right key

toNameBasedSTerm :: SFrame -> STerm -> STerm
toNameBasedSTerm frame sterm =
  case sterm of
    TName n -> TName n
    TVariable l ->
      case Map.lookup l (mapping frame) of
        Just (Atomic t)  -> do
          if l `elem` bounded frame 
            then TName t
            else TVariable l
        Just t@(Composed f args) -> 
          if l `elem` bounded frame 
            then choreoTermToSTerm t
            else TVariable l
        Nothing -> TVariable l

    TFunction f rs -> do
      let rs' = map (toNameBasedSTerm frame) rs
      TFunction f rs'

tryBindSTerm :: SFrame -> STerm -> SFrame
tryBindSTerm frame sterm = 
  case sterm of
    TVariable l ->
      case Map.lookup l (mapping frame) of
        Just (Atomic t)  -> do
          if l `elem` bounded frame 
            then frame
            else insertBoundedEntry frame l
        Just (Composed f args) -> frame
        Nothing -> frame
    TFunction f rs -> frame

choreoTermToSTerm :: Term -> STerm
choreoTermToSTerm (Atomic x) = TName x
choreoTermToSTerm (Composed f args) = TFunction f (map choreoTermToSTerm args)