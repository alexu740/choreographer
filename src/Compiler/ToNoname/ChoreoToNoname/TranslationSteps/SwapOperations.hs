module Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SwapOperations where

import Types.LocalBehavior (Label, Recipe (..))
import Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqLocalBehavior (LCenter (..), LLeft (..), LRight (..), SeqLocalBehavior (..))
import qualified Data.Set as Set

swapOperations :: SeqLocalBehavior -> SeqLocalBehavior
swapOperations (L l) = L (swapLeft l)

swapLeft :: LLeft -> LLeft
swapLeft (LChoice m l d left) =
  LChoice m l d (swapLeft left)
swapLeft (LReceive l left) =
  LReceive l (swapLeft left)
swapLeft (C center) =
  let (left, center') = swapCenter [] center
   in left $ C center'

swapCenter :: [Label] -> LCenter -> (LLeft -> LLeft, LCenter)
swapCenter ls (LTry l f rs center1 center2) =
  let (left1, center1') = swapCenter (l : ls) center1
      (left2, center2') = swapCenter ls center2
   in (left1 . left2, LTry l f rs center1' center2')
swapCenter ls (LRead l c r center) =
  let (left, center') = swapCenter (l : ls) center
   in (left, LRead l c r center')
swapCenter ls (LIf r1 r2 center1 center2) =
  let (left1, center1') = swapCenter ls center1
      (left2, center2') = swapCenter ls center2
   in (left1 . left2, LIf r1 r2 center1' center2')
swapCenter ls new@(LNew ns (LSeq (C center)))
  | null ns = swapCenter ls center
  | otherwise = case combineNew (Set.fromList ls) ns center of
      Just center' -> swapCenter [] center'
      Nothing -> (id, new)
swapCenter ls new@(LNew ns (LSeq left)) =
  case getLeftConstructor (Set.fromList ls) left of
    Just (leftF, left') ->
      let (leftF', left'') = swapCenter ls $ LNew ns (LSeq left')
       in (leftF . leftF', left'')
    Nothing -> (id, new)
swapCenter _ (LNew ns right) = (id, LNew ns $ propagateToLeft right)

getLeftConstructor :: Set.Set Label -> LLeft -> Maybe (LLeft -> LLeft, LLeft)
getLeftConstructor ls (LChoice m l d left) =
  let dependencies = any (`Set.member` ls) d
   in if not dependencies
        then Just (LChoice m l d, left)
        else Nothing
getLeftConstructor _ (LReceive l left) = Just (LReceive l, left)
getLeftConstructor _ center = Just (id, center)

combineNew :: Set.Set Label -> [Label] -> LCenter -> Maybe LCenter
combineNew ls ns (LTry l f rs center1 center2) = do
  let dependencies = any (dependent ls) rs
  center1' <- combineNew ls ns center1
  center2' <- combineNew ls ns center2
  if not dependencies
    then Just $ LTry l f rs center1' center2'
    else Nothing
combineNew ls ns (LRead l c r center) = do
  let dependencies = dependent ls r
  center' <- combineNew ls ns center
  if not dependencies
    then Just $ LRead l c r center'
    else Nothing
combineNew ls ns (LIf r1 r2 center1 center2) = do
  let dependencies = dependent ls r1 || dependent ls r2
  center1' <- combineNew ls ns center1
  center2' <- combineNew ls ns center2
  if not dependencies
    then Just $ LIf r1 r2 center1' center2'
    else Nothing
combineNew _ ns (LNew ns' right) = Just $ LNew (ns ++ ns') right

dependent :: Set.Set Label -> Recipe -> Bool
dependent ls (LAtom l) = Set.member l ls
dependent ls (LComp _ rs) = any (dependent ls) rs

propagateToLeft :: LRight -> LRight
propagateToLeft (LSend r right) = LSend r $ propagateToLeft right
propagateToLeft (LWrite c r1 r2 right) = LWrite c r1 r2 $ propagateToLeft right
propagateToLeft (LRelease m f right) = LRelease m f $ propagateToLeft right
propagateToLeft LNil = LNil
propagateToLeft (LSeq left) = LSeq $ swapLeft left
