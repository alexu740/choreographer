module Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqLocalBehavior where

import qualified Types.Simple as S
import qualified Types.LocalBehavior as LB

newtype SeqLocalBehavior
  = -- | Left local behavior
    L LLeft
  deriving (Show, Eq)

data LLeft
  = -- | Non-deterministic choice of variable.
    LChoice S.Mode LB.Label LB.Domain LLeft
  | -- | Receive.
    LReceive LB.Label LLeft
  | -- | Center local behavior
    C LCenter
  deriving (Show, Eq)

data LCenter
  = -- | Try-catch
    LTry LB.Label S.Function [LB.Recipe] LCenter LCenter
  | -- | Cell read.
    LRead LB.Label S.Cell LB.Recipe LCenter
  | -- | Conditional statement.
    LIf LB.Recipe LB.Recipe LCenter LCenter
  | -- | Fresh nonce
    LNew [LB.Label] LRight
  deriving (Show, Eq)

data LRight
  = -- | Branching send of recipes, non-empty list
    LSend LB.Recipe LRight
  | -- | Cell write.
    LWrite S.Cell LB.Recipe LB.Recipe LRight
  | -- | Privacy Release of a formula.
    LRelease S.Mode LB.Formula LRight
  | -- | End
    LNil
  | -- | Sequence
    LSeq LLeft
  deriving (Show, Eq)
