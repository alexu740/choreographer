module Types.LocalBehavior where

import Types.Simple (Identifier, Cell, Function, Mode)

-- | Label names.
type Label = Identifier

-- | A domain is a list of constants (functions of arity 0).
type Domain = [Label]

-- | A recipe is either atomic or composed with subterms.
data Recipe
  = -- | Atomic recipe.
    LAtom Label
  | -- | Composed recipe.
    LComp Function [Recipe]
  deriving (Eq, Ord, Show)

-- | A quantifier-free FOL formula.
data Formula
  = -- | Trivially true formula.
    Top
  | -- | Equality between Terms.
    Equality Recipe Recipe
  | -- | Negation.
    Neg Formula
  | -- | Conjunction.
    And Formula Formula
  deriving (Eq, Show)

data LocalAtomic
  = -- | Fresh nonce
    LNew Label LocalAtomic
  | -- | Cell read.
    LRead Label Cell Recipe LocalAtomic
  | -- | Cell write.
    LWrite Cell Recipe Recipe LocalAtomic
  | -- | Conditional statement.
    LIf Recipe Recipe LocalAtomic LocalAtomic
  | -- | Non-deterministic choice of variable.
    LChoice Mode Label Domain LocalAtomic
  | -- | Privacy Release of a formula.
    LRelease Mode Formula LocalAtomic
  | -- | Try catch statement.
    LTry Label Function [Recipe] LocalAtomic LocalAtomic
  | -- | Continue with local behavior.
    LUnlock LocalBehavior
  deriving (Show, Eq)

data LocalBehavior
  = -- | End
    LNil
  | -- | Branching send of recipes, non-empty list
    LSend [(Recipe, LocalBehavior)]
  | -- | Receive.
    LReceive Label LocalBehavior
  | -- | Continue to local atomic part.
    LLock LocalAtomic
  deriving (Show, Eq)