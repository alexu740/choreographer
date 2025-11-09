module Compiler.ToLocalBehavior.RecipeUtility where

import Types.Simple ( Cell, Constructors,  Mode (..),  FUNCTIONS(..), )
import Types.LocalBehavior (Domain, Label,LocalAtomic (..), LocalBehavior (..), Recipe (..),Formula(..))
import Types.Choreography (Agent, Term (..))
import Types.Signatures (LocalBehaviorTranslatorFunction)
import Types.Rewrite (FrameError(..), TranslationError(..), DestructorApp (..),  Checks, TranslationResult, Frame)

import qualified Types.Rewrite as State

import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as ListNonEmpty
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Bifunctor as Bifunctor
import Control.Applicative ((<|>))
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

-- | Constructs all recipes with respect to the specification.
--   I.e. find all rj's such that for all i: Fi(rj) = t_j^i
--
-- Input
-- * List of frames, i.e. [F1, ..., Fn]
-- * List of term-lists, i.e. [[t_1^1, ..., t_m1^1], ..., [t_1^n, ..., t_m^n]]
--
-- Returns
-- * 'Right' a list of recipes, if there is a uniform recipe for all frames and terms.
-- * 'Left' error, if any recipe construction fails.
constructAllRecipes :: Constructors -> [State.State] -> [[Term]] -> TranslationResult [Recipe]
constructAllRecipes constructors frames terms =
  let transposedTerms = List.transpose terms -- [[t_1^1, ..., t_1^n], ..., [t_m^1, ..., t_mn^n]]
      fts = map (zip frames) transposedTerms -- [[(F1, t_1^1), ..., , (Fn, t_1^n)], ..., [(F1, t_m^1), ..., (Fn, t_mn^n)]]
  in traverse (constructRecipe constructors) fts

-- | Constructs a recipes with respect to the specification.
--   I.e. find rj such that for all i: Fi(rj) = t_j^i
--
-- Input
-- * List of frame-term pairs, i.e. [(F1, t_j^1), ..., , (Fn, t_j^n)]
--
-- Returns
-- * 'Right' a recipe, if there is a uniform recipe for all frames and terms.
-- * 'Left' error, no recipe exists, or the input list is empty.
constructRecipe :: Constructors -> [(State.State, Term)] -> TranslationResult Recipe
constructRecipe _ [] = Left UndefinedError
constructRecipe constructors ls@(ft : fts) =
  let nonEmptyList = ft :| fts
      recipes = ListNonEmpty.map (uncurry $ composeSet constructors) nonEmptyList
      commonRecipe = foldl1 Set.intersection recipes
   in if Set.null commonRecipe
        then Left . NoRecipe $ map (Bifunctor.first State.frame) ls
        else Right (Set.elemAt 0 commonRecipe)

removeRecipesFromState :: State.State -> Recipe -> State.State
removeRecipesFromState state recipe =
  let labels = collectLabels recipe
      frame = State.frame state
      frame' = Map.filterWithKey (\k _ -> k `Set.notMember` labels) frame
   in state {State.frame = frame'}

collectLabels :: Recipe -> Set.Set Label
collectLabels (LComp SESSION subterms) = case subterms of
  [_, LAtom l] -> Set.singleton l
  (_ : ts) -> Set.unions $ map collectLabels ts
  _ -> Set.empty
collectLabels (LComp PAIR subterms) = case subterms of
  (LAtom l : ts) -> Set.unions $ Set.singleton l : map collectLabels ts
  _ -> Set.empty
collectLabels _ = Set.empty


-- | Returns one recipe for composing the term in given a frame.
compose :: Constructors -> State.State -> Term -> Maybe Recipe
compose constructors state term =
  composeDirectly frame term <|> composeRecipe knownRecipes term <|> composeRecursive constructors state term
  where
    frame = State.frame state
    knownRecipes =  State.boundedRecipes state

-- | Helper function for compose.
-- If frame = [..., Xi |-> term', ...], for some Xi and term = term', then return Just Xi.
-- Otherwise, return Nothing.
composeDirectly :: Frame -> Term -> Maybe Recipe
composeDirectly frame term =
  fmap LAtom . Maybe.listToMaybe . Map.keys $ Map.filter (== term) frame

-- | Helper function for compose.
-- Return all bounded recipes.
composeRecipe :: Set.Set (Recipe, Term) -> Term -> Maybe Recipe
composeRecipe recipes term =
  Maybe.listToMaybe . Set.toList . Set.map fst $ Set.filter (\(_, t) -> t == term) recipes

-- | Helper function for compose.
-- If frame = [..., Xi |-> term', ...], for some Xi and term = term', then return Just Xi.
-- Otherwise, return Nothing.
composeRecursive :: Constructors -> State.State -> Term -> Maybe Recipe
composeRecursive constructors state (Composed func subterms)
  | Just arity <- Map.lookup func constructors,
    length subterms == arity =
      LComp func <$> traverse (compose constructors state) subterms
composeRecursive constructors _ (Atomic var)
  | Just arity <- Map.lookup (UnDef var) constructors,
    arity == 0 =
      Just $ LAtom var
composeRecursive _ _ _ = Nothing

-- | Returns all recipes for composing the term in given a frame.
composeSet :: Constructors -> State.State -> Term -> Set.Set Recipe
composeSet constructors state term =
  Set.unions
    [ composeDirectlySet frame term,
      composeRecipeSet knownRecipes term,
      composeRecursiveSet constructors state term
    ]
  where
    frame =  State.frame state
    knownRecipes =  State.boundedRecipes state

-- | Helper function for compose.
-- Return all Xi's such that [Xi |-> term'] ∈ frame and term = term'.
composeDirectlySet :: Frame -> Term -> Set.Set Recipe
composeDirectlySet frame term =
  Set.map LAtom . Map.keysSet $ Map.filter (== term) frame

-- | Helper function for compose.
-- Return all bounded recipes.
composeRecipeSet :: Set.Set (Recipe, Term) -> Term -> Set.Set Recipe
composeRecipeSet recipes term =
  Set.map fst $ Set.filter (\(_, t) -> t == term) recipes

-- | Helper function for compose.
-- Return all composable functions,
--  if term = f(t1, ..., tn) and f is a constructor, and t1,...,tn can be composed
composeRecursiveSet :: Constructors -> State.State -> Term -> Set.Set Recipe
composeRecursiveSet constructors state (Composed func subterms)
  | Just arity <- Map.lookup func constructors,
    length subterms == arity =
      let subtermsComposed = map (composeSet constructors state) subterms
      in if any Set.null subtermsComposed
            then Set.empty
            else Set.map (LComp func) (combineRecipes subtermsComposed)
composeRecursiveSet constructors _ (Atomic var)
  | Just arity <- Map.lookup (UnDef var) constructors,
    arity == 0 =
      Set.singleton (LAtom var)
composeRecursiveSet _ _ _ = Set.empty

combineRecipes :: [Set.Set Recipe] -> Set.Set [Recipe]
combineRecipes ls =
  Set.fromList . combineRecipesHelper $ map Set.toList ls

combineRecipesHelper :: [[Recipe]] -> [[Recipe]]
combineRecipesHelper [] = [[]]
combineRecipesHelper (xs : xss) =
  [x : rest | x <- xs, rest <- combineRecipesHelper xss]