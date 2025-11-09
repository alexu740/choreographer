module Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqToNoname where

import qualified Types.Choreography as Choreo
import Types.Rewrite (Frame)
import Syntax.Util (toText)
import qualified Types.LocalBehavior as LB
import qualified Types.Simple as S
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqLocalBehavior as SeqLB
import qualified Data.Map as Map
import qualified Compiler.ToNoname.Noname.Syntax as Noname

-- | Converts a sequentialized local behavior into a Noname process.
toNonameSeq :: Frame -> SeqLB.SeqLocalBehavior -> Noname.Process
toNonameSeq frame seqLB = case seqLB of
  SeqLB.L lleft -> Noname.Pl $ toNonameLeft frame lleft

-- | Converts the left part of a sequentialized local behavior to a Noname left process.
toNonameLeft :: Frame -> SeqLB.LLeft -> Noname.LeftProcess
toNonameLeft frame lcenter = case lcenter of
  SeqLB.LChoice m lb dom ll ->
    Noname.Choice (toNonameMode m) lb dom (toNonameLeft frame ll)
  SeqLB.LReceive lb ll ->
    Noname.Receive lb (toNonameLeft frame ll)
  SeqLB.C lc ->
    Noname.Center (toNonameCenter frame lc)

-- | Converts the center part of a sequentialized local behavior to a Noname center process.
toNonameCenter :: Frame -> SeqLB.LCenter -> Noname.CenterProcess
toNonameCenter frame lcenter = case lcenter of
  SeqLB.LTry lb f rs lc1 lc2 ->
    Noname.Try
      lb
      (toNonameFunc f)
      (map (toNonameRecipe frame) rs)
      (toNonameCenter frame lc1)
      (toNonameCenter frame lc2)
  SeqLB.LRead lb c r lc ->
    Noname.Read
      lb
      c
      (toNonameRecipe frame r)
      (toNonameCenter frame lc)
  SeqLB.LIf r1 r2 lc1 lc2 ->
    Noname.If
      (Noname.Equality (toNonameRecipe frame r1) (toNonameRecipe frame r2))
      (toNonameCenter frame lc1)
      (toNonameCenter frame lc2)
  SeqLB.LNew ls lr ->
    Noname.New ls (toNonameRight frame lr)

-- | Converts the right part of a sequentialized local behavior to a Noname right process.
toNonameRight :: Frame -> SeqLB.LRight -> Noname.RightProcess
toNonameRight frame lright = case lright of
  SeqLB.LSend r lr -> Noname.Send (toNonameRecipe frame r) (toNonameRight frame lr)
  SeqLB.LWrite c r1 r2 lr ->
    Noname.Write
      c
      (toNonameRecipe frame r1)
      (toNonameRecipe frame r2)
      (toNonameRight frame lr)
  SeqLB.LRelease m f lr ->
    Noname.Release
      (toNonameMode m)
      (toNonameFormula frame f)
      (toNonameRight frame lr)
  SeqLB.LNil -> Noname.Nil
  SeqLB.LSeq ll -> Noname.Sequence (toNonameLeft frame ll)

-- | Converts a formula from the local behavior language to the Noname representation.
toNonameFormula :: Frame -> LB.Formula -> Noname.Formula
toNonameFormula frame formula = case formula of
  LB.Top -> Noname.Top
  LB.Equality r1 r2 -> Noname.Equality (toNonameRecipe frame r1) (toNonameRecipe frame r2)
  LB.Neg f -> Noname.Neg (toNonameFormula frame f)
  LB.And f1 f2 -> Noname.And (toNonameFormula frame f1) (toNonameFormula frame f2)

-- | Converts a recipe (message expression) to a Noname message.
toNonameRecipe :: Frame -> LB.Recipe -> Noname.Message
toNonameRecipe frame (LB.LAtom l) =
  let msg =
        case Map.lookup l frame of
          Just t -> toNonameMessage t
          _ -> Noname.Atom l
   in msg
toNonameRecipe frame (LB.LComp f rs) =
  Noname.Comp (toNonameFunc f) (map (toNonameRecipe frame) rs)

-- | Converts a local function into a Noname function representation (as text).
toNonameFunc :: S.Function -> Noname.Function
toNonameFunc = toText

-- | Converts a mode (e.g., ♦ or *) to the corresponding Noname mode.
toNonameMode :: S.Mode -> Noname.Mode
toNonameMode S.Star = Noname.Star
toNonameMode S.Diamond = Noname.Diamond

toNonameMessage :: Choreo.Term -> Noname.Message
toNonameMessage (Choreo.Atomic a) = Noname.Atom a
toNonameMessage (Choreo.Composed f ts) =
  Noname.Comp (toNonameFunc f) (map toNonameMessage ts)
