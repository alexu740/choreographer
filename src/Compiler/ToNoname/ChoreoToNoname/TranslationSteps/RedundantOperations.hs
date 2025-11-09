module Compiler.ToNoname.ChoreoToNoname.TranslationSteps.RedundantOperations (removeRedundantOperations) where

import Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqLocalBehavior (LCenter (..), LLeft (..), LRight (..), SeqLocalBehavior (..))

removeRedundantOperations :: SeqLocalBehavior -> SeqLocalBehavior
removeRedundantOperations (L left) = L $ removeRedundantOperationsLeft left

removeRedundantOperationsLeft :: LLeft -> LLeft
removeRedundantOperationsLeft (LChoice mode label dom left) =
  case removeRedundantOperationsLeft left of
    C (LNew [] LNil) -> C (LNew [] LNil)
    left' -> LChoice mode label dom left'
removeRedundantOperationsLeft (LReceive label left) =
  case removeRedundantOperationsLeft left of
    C (LNew [] LNil) -> C (LNew [] LNil)
    left' -> LReceive label left'
removeRedundantOperationsLeft (C center) =
  C $ removeRedundantOperationsCenter center

removeRedundantOperationsCenter :: LCenter -> LCenter
removeRedundantOperationsCenter (LTry label func r2 lc1 lc2) =
  case (removeRedundantOperationsCenter lc1, removeRedundantOperationsCenter lc2) of
    (LNew [] LNil, LNew [] LNil) -> LNew [] LNil
    (lc1', lc2') -> LTry label func r2 lc1' lc2'
removeRedundantOperationsCenter (LRead label cell r lc) =
  case removeRedundantOperationsCenter lc of
    LNew [] LNil -> LNew [] LNil
    lc' -> LRead label cell r lc'
removeRedundantOperationsCenter (LIf r1 r2 lc1 lc2) =
  case (removeRedundantOperationsCenter lc1, removeRedundantOperationsCenter lc2) of
    (LNew [] LNil, LNew [] LNil) -> LNew [] LNil
    (lc1', lc2') -> LIf r1 r2 lc1' lc2'
removeRedundantOperationsCenter (LNew ls right) =
  case removeRedundantOperationsRight right of
    LNil -> LNew [] LNil
    right' -> LNew ls right'

removeRedundantOperationsRight :: LRight -> LRight
removeRedundantOperationsRight (LSeq left) =
  case removeRedundantOperationsLeft left of
    C (LNew [] LNil) -> LNil
    left' -> LSeq left'
removeRedundantOperationsRight (LSend r right) =
  LSend r (removeRedundantOperationsRight right)
removeRedundantOperationsRight (LWrite cell r1 r2 right) =
  LWrite cell r1 r2 (removeRedundantOperationsRight right)
removeRedundantOperationsRight (LRelease mode formula right) =
  LRelease mode formula (removeRedundantOperationsRight right)
removeRedundantOperationsRight LNil = LNil
