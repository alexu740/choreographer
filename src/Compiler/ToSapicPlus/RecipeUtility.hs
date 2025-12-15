{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.RecipeUtility where

import Types.Simple ( Cell,  Mode (..),  FUNCTIONS(..))
import Types.LocalBehavior (Domain, Label,LocalAtomic (..), LocalBehavior (..), Recipe (..),Formula(..))
import Types.Choreography (Agent, Term (..))
import Types.Signatures (LocalBehaviorTranslatorFunction)
import Types.Rewrite (FrameError(..), TranslationError(..), DestructorApp (..),  Checks, TranslationResult, Frame)
import Types.ChoreographyProtocolShell (ProtocolDescription)

import Compiler.ToSapicPlus.RewriteSystem.RewriteSystem (RewriteSystem(..), getRewriteSystem)

import Debug.Trace (trace, traceM, traceShowId, traceShow)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)

import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as ListNonEmpty
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Bifunctor as Bifunctor
import Control.Applicative ((<|>))
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Text as T

import Compiler.ToSapicPlus.SFrame (SFrame(mapping), insertTermsInFrame, getLatestFrameKey, toNameBasedSTerm)
import Types.Sapic(SConstructors, SRecipe(..), SVariable, SapicTranslationError, STerm(..))
import Compiler.ToSapicPlus.RewriteSystem.EquationalTheoryExtension (findEquivalenceClass, composeViaEquivalenceClassSet, operations)

---------------------------------
recipeToTerm :: SRecipe -> STerm
recipeToTerm (RVariable var) = TVariable var
recipeToTerm (RFunction f args) = TFunction f (map recipeToTerm args)

recipeToNameTerm :: (SFrame, SRecipe) -> STerm
recipeToNameTerm (frame, RVariable var) = toNameBasedSTerm frame (TVariable var) -- choreoTermToSTerm $ mapping frame Map.! var
recipeToNameTerm (frame, RFunction f []) = TFunction f []
recipeToNameTerm (frame, RFunction f args) = TFunction f (map (recipeToNameTerm . h frame) args) -- was recipeToTerm before

choreoTermToSTerm :: Term -> STerm
choreoTermToSTerm (Atomic x) = TName x
choreoTermToSTerm (Composed f args) = TFunction f (map choreoTermToSTerm args)

h :: SFrame -> SRecipe -> (SFrame, SRecipe)
h frame recipe = (frame, recipe)
---------------------------------
---------------------------------
-- | Constructs a recipes with respect to the specification.
--   I.e. find rj such that for all i: Fi(rj) = t_j^i
--
-- Input
-- * List of frame-term pairs, i.e. [(F1, t_j^1), ..., , (Fn, t_j^n)]
--
-- Returns
-- * 'Right' a recipe, if there is a uniform recipe for all frames and terms.
-- * 'Left' error, no recipe exists, or the input list is empty.
constructCommmonRecipe :: ProtocolDescription ->  [(SFrame, Term)] -> Either SapicTranslationError SRecipe
constructCommmonRecipe _ [] = Left "UndefinedError: Cannot construct recipe for empty frame-term list"
constructCommmonRecipe description ls@(ft : fts) =
  let nonEmptyList = ft :| fts
      constructors = systemConstructors (getRewriteSystem description)
      recipes = ListNonEmpty.map (uncurry (composeSet constructors)) nonEmptyList
      commonRecipe = foldl1 Set.intersection recipes
   in if Set.null commonRecipe
        then Left ("NoCommonRecipe: " <> T.pack (show $ map (Bifunctor.first mapping) ls))
        else Right (Set.elemAt 0 commonRecipe)
---------------------------------
---------------------------------
-- | Returns all recipes for composing the term in given a frame.
composeSet :: SConstructors -> SFrame -> Term -> Set.Set SRecipe
composeSet constructors state term = do
  let equivClassMembers = findEquivalenceClass [] term
  let equivRecipesSets = map (composeRecursiveSet constructors state) equivClassMembers
  let directRecipeSets = map (composeDirectlySet frame) equivClassMembers
  let equivRecipes = Set.unions equivRecipesSets
  let directRecipes = Set.unions directRecipeSets

  Set.unions
    [ --composeDirectlySet frame term,
      directRecipes,
--      composeViaEquivalenceClassSet frame term,
      equivRecipes,
      composeRecipeSet knownRecipes term
--      composeRecursiveSet constructors state term
    ]
  where
    frame = mapping state
    knownRecipes = Set.empty

-- | Helper function for compose.
-- Return all Xi's such that [Xi |-> term'] ∈ frame and term = term'.
composeDirectlySet :: Map.Map SVariable Term -> Term -> Set.Set SRecipe
composeDirectlySet frame term =
  Set.map RVariable . Map.keysSet $ Map.filter (== term) frame

-- | Helper function for compose.
-- Return all bounded recipes.
composeRecipeSet :: Set.Set (SRecipe, Term) -> Term -> Set.Set SRecipe
composeRecipeSet recipes term =
  Set.map fst $ Set.filter (\(_, t) -> t == term) recipes

-- | Helper function for compose.
-- Return all composable functions,
--  if term = f(t1, ..., tn) and f is a constructor, and t1,...,tn can be composed
composeRecursiveSet :: SConstructors -> SFrame -> Term -> Set.Set SRecipe
composeRecursiveSet constructors state (Composed func subterms)
  | Just arity <- Map.lookup func (constructors `Map.union` Map.fromList operations),
    length subterms == arity =
      if arity == 0
        then
          Set.fromList [RFunction func []]
        else
          let subtermsComposed = map (composeSet constructors state) subterms
          in if any Set.null subtermsComposed
                then Set.empty
                else Set.map (RFunction func) (combineRecipes subtermsComposed)
composeRecursiveSet constructors _ (Atomic var)
  | Just arity <- Map.lookup (UnDef var) constructors,
    arity == 0 =
      Set.singleton (RVariable var)
composeRecursiveSet _ _ _ = Set.empty
---------------------------------
---------------------------------
combineRecipes :: [Set.Set SRecipe] -> Set.Set [SRecipe]
combineRecipes ls =
  Set.fromList . combineRecipesHelper $ map Set.toList ls

combineRecipesHelper :: [[SRecipe]] -> [[SRecipe]]
combineRecipesHelper [] = [[]]
combineRecipesHelper (xs : xss) =
  [x : rest | x <- xs, rest <- combineRecipesHelper xss]

---------------------------------
---------------------------------
-- | Returns one recipe for composing the term in given a frame.
compose :: ProtocolDescription -> SFrame -> Term -> Maybe SRecipe
compose description frame term =
  composeDirectly frame term <|> 
  composeRecipe knownRecipes term <|> 
  composeViaEquivalenceClass description frame term <|> 
  composeRecursive description constructors frame term
  where
    constructors = systemConstructors (getRewriteSystem description)
    knownRecipes = Set.empty

-- | Helper function for compose.
-- If frame = [..., Xi |-> term', ...], for some Xi and term = term', then return Just Xi.
-- Otherwise, return Nothing.
composeDirectly :: SFrame -> Term -> Maybe SRecipe
composeDirectly frame term =
  fmap RVariable . Maybe.listToMaybe . Map.keys $ Map.filter (== term) (mapping frame)

-- | Helper function for compose.
-- Return all bounded recipes.
composeRecipe :: Set.Set (SRecipe, Term) -> Term -> Maybe SRecipe
composeRecipe recipes term =
  Maybe.listToMaybe . Set.toList . Set.map fst $ Set.filter (\(_, t) -> t == term) recipes

-- | Helper function for compose.
-- If frame = [..., Xi |-> term', ...], for some Xi and term = term', then return Just Xi.
-- Otherwise, return Nothing.
composeRecursive :: ProtocolDescription -> SConstructors -> SFrame -> Term -> Maybe SRecipe
composeRecursive description constructors state (Composed func subterms)
  | Just arity <- Map.lookup func (constructors `Map.union` Map.fromList operations),
    length subterms == arity =
      if arity == 0
        then
          Just $ RFunction func []
        else
          RFunction func <$> traverse (compose description state) subterms
composeRecursive description constructors _ (Atomic var)
  | Just arity <- Map.lookup (UnDef var) (constructors `Map.union` Map.fromList operations),
    arity == 0 =
      Just $ RVariable var
composeRecursive _ _ _ _ = Nothing



composeNoEquiv :: ProtocolDescription -> SFrame -> Term -> Maybe SRecipe
composeNoEquiv description frame term =
  let constructors = systemConstructors (getRewriteSystem description)
  in  composeDirectly frame term
   <|> composeRecursive description constructors frame term

composeViaEquivalenceClass :: ProtocolDescription -> SFrame -> Term -> Maybe SRecipe
composeViaEquivalenceClass description frame t =
  firstJust
    [ composeNoEquiv description frame rep | rep <- findEquivalenceClass [] t
    ]

firstJust :: [Maybe a] -> Maybe a
firstJust = Maybe.listToMaybe . Maybe.catMaybes