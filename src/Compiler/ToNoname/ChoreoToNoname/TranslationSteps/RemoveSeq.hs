module Compiler.ToNoname.ChoreoToNoname.TranslationSteps.RemoveSeq where

import Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqLocalBehavior (LCenter (..), LLeft (..), LRight (..), SeqLocalBehavior (..))
import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NE

removeSeq :: SeqLocalBehavior -> NonEmpty SeqLocalBehavior
removeSeq (L l) = NE.map L $ splitLeft l

splitLeft :: LLeft -> NonEmpty LLeft
splitLeft (LChoice m v d l) = NE.map (LChoice m v d) $ splitLeft l
splitLeft (LReceive v l) = NE.map (LReceive v) $ splitLeft l
splitLeft (C c) = NE.map C $ splitCenter c

splitCenter :: LCenter -> NonEmpty LCenter
splitCenter (LTry v f args c1 c2) =
  let c1s = splitCenter c1
      c2s = splitCenter c2
   in liftA2 (LTry v f args) c1s c2s
splitCenter (LRead v c m c') = splitWith splitCenter (LRead v c m) c'
splitCenter (LIf r1 r2 c1 c2) =
  let c1s = splitCenter c1
      c2s = splitCenter c2
   in liftA2 (LIf r1 r2) c1s c2s
splitCenter (LNew vs r) =
  let r' = splitRight r
   in LNew vs (NE.head r') :| map (LNew []) (NE.tail r')

splitRight :: LRight -> NonEmpty LRight
splitRight right = case right of
  LNil -> LNil :| []
  LSeq l -> LNil <| NE.map LSeq (splitLeft l)
  LSend m r -> splitWith splitRight (LSend m) r
  LWrite c m1 m2 r -> splitWith splitRight (LWrite c m1 m2) r
  LRelease m f r -> splitWith splitRight (LRelease m f) r

splitWith :: (a -> NonEmpty a) -> (a -> a) -> a -> NonEmpty a
splitWith recf constr x =
  let xs = recf x
   in constr (NE.head xs) :| NE.tail xs
