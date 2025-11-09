module Types.Choreography where

import Types.Simple(Identifier, Cell, Function, Mode)
import Types.LocalBehavior(Domain) -- Problematic
import qualified Data.Map as Map

-- | Agent names.
type Agent = Identifier

-- | Variable names.
type Variable = Identifier

-- | A term is either atomic or composed with subterms.
data Term
  = -- | Atmoic term.
    Atomic Variable
  | -- | Composed term.
    Composed Function [Term]
  deriving (Eq, Ord, Show)

-- | A quantifier-free FOL formula.
data Formula
  = -- | Trivially true formula.
    Top
  | -- | Equality between Terms.
    Equality Term Term
  | -- | Negation.
    Neg Formula
  | -- | Conjunction.
    And Formula Formula
  deriving (Eq, Show)
  
-- | A choreography
data Choreography = 
  Interaction Agent Agent [(Term, Choreography)] CDefault | -- ^ Interaction of Term(s), non-empty list.
  Lock Agent Atomic | -- ^ Continue with atomic part.
  Nil |
  StateHint (Map.Map Agent [Term]) Choreography  -- ^ Internal state hint.
  deriving (Show, Eq)
  
-- | An atomic part of a choreography
data Atomic
  = -- | Fresh nonce.
    Nonce Variable Atomic
  | -- | Cell read
    Read Variable Cell Term Atomic
  | -- | Cell write.
    Write Cell Term Term Atomic
  | -- | Conditional statement.
    If Term Term Atomic Atomic
  | -- | Non-deterministic choice of variable.
    Choice Mode Variable Domain Atomic
  | -- | Privacy Release of a formula.
    Release Mode Formula Atomic
  | -- | Continue with choreography.
    Unlock Choreography
  deriving (Show, Eq)

-- | A default case after an interaction of a choreograhy
data CDefault
  = 
    Epsilon -- ^ Empty default.
  | Otherwise Choreography -- ^ Default case.
  deriving (Show, Eq)