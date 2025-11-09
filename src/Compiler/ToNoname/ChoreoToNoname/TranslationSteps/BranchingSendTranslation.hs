{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToNoname.ChoreoToNoname.TranslationSteps.BranchingSendTranslation (removeBranchingSend) where

import Types.Simple (Mode (..))
import Types.LocalBehavior (Label, LocalAtomic (..), LocalBehavior (..),  Recipe (..))
import qualified Data.Text as T

-- | Removes branching send constructs from a local behavior.
--
-- Branching sends are translated into labeled choices followed by a
-- sequence of conditional sends.
removeBranchingSend :: LocalBehavior -> LocalBehavior
removeBranchingSend = removeBranchingSendLocal 0

-- | Internal helper for 'removeBranchingSend' that tracks recursion depth
-- with a counter used to generate fresh labels.
removeBranchingSendLocal :: Int -> LocalBehavior -> LocalBehavior
removeBranchingSendLocal count (LSend ls) = translateSend count (LSend ls)
removeBranchingSendLocal count lb =
  let fa = removeBranchingSendAtomic count
      fb = removeBranchingSendLocal count
   in mapLocalBehavior fa fb lb

-- | Recursively transforms branching sends in atomic local behavior.
removeBranchingSendAtomic :: Int -> LocalAtomic -> LocalAtomic
removeBranchingSendAtomic count latom =
  let fa = removeBranchingSendAtomic count
      fb = removeBranchingSendLocal count
   in mapLocalAtomic fa fb latom

-- | Translates a send with multiple branches into a choice-based conditional structure.
--
-- * If there is only one branch, it is processed normally.
-- * If multiple branches exist, a labeled choice is introduced and each
--   branch is wrapped in an if-condition.
translateSend :: Int -> LocalBehavior -> LocalBehavior
translateSend count (LSend rlb) =
  case rlb of
    [(r, lb)] -> LSend [(r, removeBranchingSendLocal count lb)]
    _ ->
      let numberedrlb = zip (map (T.pack . ("N" ++) . show) [0 :: Int ..]) rlb
          label = T.pack ("B" ++ show count)
          choice = LChoice Diamond label (map fst numberedrlb)
       in LLock . choice $ constructIfs (count + 1) label numberedrlb
translateSend _ x = x

-- | Constructs a nested sequence of if-conditionals for each send branch.
--
-- This is used when transforming a multi-branch send into a conditional
-- sequence under a labeled choice.
constructIfs :: Int -> Label -> [(Label, (Recipe, LocalBehavior))] -> LocalAtomic
constructIfs count label numberedrlb =
  case numberedrlb of
    [] -> LUnlock LNil
    [(_, (r, lb))] ->
      LUnlock $ LSend [(r, removeBranchingSendLocal count lb)]
    ((no, (r, lb)) : ls) ->
      let ifs =
            LIf
              (LAtom label)
              (LAtom no)
              (LUnlock $ LSend [(r, removeBranchingSendLocal count lb)])
       in ifs $ constructIfs count label ls


mapLocalBehavior :: (LocalAtomic -> LocalAtomic) -> (LocalBehavior -> LocalBehavior) -> LocalBehavior -> LocalBehavior
mapLocalBehavior fa fb localBehavior =
  case localBehavior of
    LNil -> LNil
    LSend lbs -> LSend $ map fst lbs `zip` map (fb . snd) lbs
    LReceive l lb -> LReceive l $ fb lb
    LLock la -> LLock $ fa la

mapLocalAtomic :: (LocalAtomic -> LocalAtomic) -> (LocalBehavior -> LocalBehavior) -> LocalAtomic -> LocalAtomic
mapLocalAtomic fa fb localAtom =
  case localAtom of
    LNew l la -> LNew l $ fa la
    LRead l cell r la -> LRead l cell r $ fa la
    LWrite cell r1 r2 la -> LWrite cell r1 r2 $ fa la
    LIf r1 r2 la1 la2 -> LIf r1 r2 (fa la1) (fa la2)
    LChoice m l dom la -> LChoice m l dom $ fa la
    LRelease m f la -> LRelease m f $ fa la
    LTry l f rs la1 la2 -> LTry l f rs (fa la1) (fa la2)
    LUnlock lb -> LUnlock $ fb lb