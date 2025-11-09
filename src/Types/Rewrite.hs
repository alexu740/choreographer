module Types.Rewrite where

import Types.Simple (Function, Constructors)
import Types.Choreography (Agent, Variable, Term)
import Types.LocalBehavior (Label, Recipe)
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.Set as Set

-- | Variables used in rewrite patterns for destructors and verifiers.
data RewriteVar = KEY | MSG | RANDOM | PAIR1 | PAIR2 | UnDef T.Text deriving (Show, Read, Eq, Ord)

-- | A term used in rewrite rules, allowing variable placeholders.
data RewriteTerm
  = -- | Rewrite variable.
    RewriteVar RewriteVar
  | -- | Atmoic term.
    Atom Variable
  | -- | Composed term.
    Comp Function [RewriteTerm]
  deriving (Eq, Ord, Show)

-- | A pattern for matching terms in rewrite rules.
type Pattern = [RewriteTerm]

-- | A replacement term for rewrite rules.
type Replacement = RewriteTerm

-- | A rewrite rule consists of a pattern and a replacement.
type RewriteRule = (Pattern, Replacement)

-- | A collection of rewrite rules, mapping function symbols to their patterns and replacements.
type RewriteRules = Map.Map Function RewriteRule

data Description = Description
  { 
    agent :: Agent,
    constructors :: Constructors,
    rewriteRules :: RewriteRules
  }
  deriving (Show, Eq)

-- | A 'Binding' is a substitution from rewrite variables to concrete terms.
type Binding = Map.Map RewriteVar Term

-- | A destructor application.
--   * dlabel: The label of resulting term after destruction.
--   * ddestructor: The destructor function applied.
--   * dsubterms: The subterms for applying the destructor on.
data DestructorApp
  = DestructorApp
  { dlabel :: Label,
    ddestructor :: Function,
    dsubterms :: [Recipe]
  }
  deriving (Show, Eq)

-- | The result of trying to rewrite a term.
type RewriteOutcome = Either RuleApplicationError RewriteSuccess

-- | A successful rewrite result.
--   * Int: The next fresh label index to use.
--   * State: The updated state after applying the rewrite.
--   * Labels: The labels of the new terms as a result of rewriting.
--   * DestructorApps: The destructor applications generated during the rewrite.
--   * Maybe Term : An optional session ID term if applicable.
type RewriteSuccess = (Int, State, [Label], [DestructorApp], Maybe Term)

-- | A single successful rewrite result.
type SingleRewriteSuccess = (Label, Term, DestructorApp, Maybe Term)

-- | A symbolic equation expressed as a pair of recipes.
type Check = (Recipe, Recipe)

-- | A list of symbolic equation (checks).
type Checks = [Check]

type Destructed = Set.Set Label

-- | A 'Frame' is a mapping from labels to terms.
type Frame = Map.Map Label Term

data State = State
  { frame :: Frame,
    unboundedTerms :: [RewriteTerm],
    boundedRecipes :: Set.Set (Recipe, Term),
    prevDestructed :: Destructed,
    prevChecks :: Checks,
    sessionID :: Maybe Term
  }
  deriving (Show, Eq)

-- | Tracks analysis progress during Phase 1 of the analysis algorithm.
--   * lnew: Labels of terms that are pending analysis.
--   * lhold: Labels temporarily on hold for re-analysis if new terms are discovered.
--   * ldone: Labels of terms that have already been analyzed.
data AnalyseState
  = AnalyseState
  { lnew :: [Label],
    lhold :: [Label],
    ldone :: [Label]
  }

-- | Error result of applying a rule to a term.
-- Indicates why the analysis has failed.
data RuleApplicationError
  = TermNotAnalyzed
  | TermNotComposable Term
  deriving (Show, Eq)

  -- | Frame errors
data FrameError
  = UndefinedLabel (Frame, Label)
  | UndefinedRewriteVar RewriteVar
  | NonMatchingPattern
  | NonMergeableBindings
  deriving (Show, Eq)

-- | Translation errors
data TranslationError
  = DifferentTypes String
  | DifferentBranchLength
  | DifferentAgents Agent Agent
  | NoRecipe [(Frame, Term)]
  | Unreachable
  | UndefinedError
  | FrameError FrameError
  deriving (Show, Eq)

type TranslationResult = Either TranslationError