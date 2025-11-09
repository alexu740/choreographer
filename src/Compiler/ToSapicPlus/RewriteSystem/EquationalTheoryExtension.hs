{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.RewriteSystem.EquationalTheoryExtension where

import Types.Simple (Function, FUNCTIONS(..))
import Types.Sapic (SVariable, SRecipe (RVariable))
import Types.Choreography (Term(..))
import Compiler.ToSapicPlus.SFrame (SFrame(..))
import qualified Data.Text as T
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe ( catMaybes ) 
import Compiler.ToSapicPlus.RewriteSystem.RewriteSystem (RewriteSystem(..))
import qualified Data.Maybe as Maybe

import Debug.Trace (trace, traceM, traceShowId, traceShow)
import Debug.Pretty.Simple (pTraceShowId, pTraceM)
import Text.Pretty.Simple (pShow)


data ETerm
  = EVar T.Text
  | EOperation Function [ETerm]
  deriving (Eq, Ord, Show)

data Equation = Equation 
  {
    lhs :: ETerm,
    rhs :: ETerm
  } deriving (Eq, Ord, Show)

operations :: [(Function, Int)]
operations = [(MULT, 2), (EXP,2)]

equationalTheory :: [Equation]
equationalTheory = [
    Equation {
      lhs = EOperation MULT [EVar "T1", EVar "T2"],
      rhs = EOperation MULT [EVar "T2", EVar "T1"]
    },
    Equation {
      lhs = EOperation MULT [EVar "T1", EOperation MULT [EVar "T2", EVar "T3"]],
      rhs = EOperation MULT [EOperation MULT [EVar "T1", EVar "T2"], EVar "T3"]
    },
    Equation {
      lhs = EOperation EXP [EOperation EXP [EVar "T1", EVar "T2"], EVar "T3"],
      rhs = EOperation EXP [EVar "T1", EOperation MULT [EVar "T2", EVar "T3"]]
    }
  ]

getFrameKeyForTerm :: SFrame -> Term -> Maybe SVariable
getFrameKeyForTerm frame term =
  fmap fst (List.find ((== term) . snd) (Map.toList (mapping frame)))

termIsComposableModuloTheory :: RewriteSystem -> SFrame -> Term -> Bool
termIsComposableModuloTheory rs frame term = 
  case term of
  Atomic k -> 
    case getFrameKeyForTerm frame (Atomic k) of
      Just k -> True
      Nothing -> False
  (Composed constructor []) ->
    let allowedContructors = Set.toList $ Map.keysSet $ systemConstructors rs
        operationSymbols = map fst operations
    in constructor `elem` (allowedContructors ++ operationSymbols)
  composedTerm -> do
    let equivClass = findEquivalenceClass [] composedTerm
    any (composableTerm rs frame) equivClass
  where
    composableTerm :: RewriteSystem -> SFrame -> Term -> Bool
    composableTerm rs frame term@(Composed constructor args) =
      case getFrameKeyForTerm frame term of
        Just k -> True
        _ -> do
          let allowedContructors = Set.toList $ Map.keysSet $ systemConstructors rs
          let operationSymbols = map fst operations
          if constructor `elem` (allowedContructors ++ operationSymbols)
            then all (termIsComposableModuloTheory rs frame) args
            else False

findEquivalenceClass :: [Term] -> Term -> [Term]
findEquivalenceClass alreadyFound term =
  let visited0 = Set.fromList alreadyFound
  in go visited0 [term] [] -- do BFS
  where
    -- BFS kind of exploration. also we need to keep a set with visited elements
    go :: Set.Set Term -> [Term] -> [Term] -> [Term]
    go _ [] acc = reverse acc
    go visited (t:queue) acc
      | t `Set.member` visited = go visited queue acc
      | otherwise =
          let newNeighbors = oneStepEquivs t
              newNeighbors' = map (nestedEquivs $ Set.toList visited) newNeighbors
              queue' = queue ++ concat newNeighbors'
              visited' = Set.insert t visited
          in go visited' queue' (t:acc)

    -- one-step equivalents, by applying any equation that matches at the top
    oneStepEquivs :: Term -> [Term]
    oneStepEquivs t@(Composed f _)
      | f `elem` map fst operations =
          let receipts = catMaybes [ matchWithEquation eq t | eq <- equationalTheory ]
          in  [ equivalentTerm r | r <- receipts ]
      | otherwise = []
    oneStepEquivs _ = []

    nestedEquivs :: [Term] -> Term -> [Term]
    nestedEquivs visited t@(Composed f args) = do
      let acc = []
      let e = map (findEquivalenceClass visited) args
      let possibleArgs = sequence e
      let nestedEquivTerms = [Composed f arguments | arguments <- possibleArgs]
      nestedEquivTerms

data EquivalenceReceipt 
  = EquivalenceReceipt {
    term :: Term,
    equation :: Equation,
    matchesLhs :: Bool,
    matchesRhs :: Bool,
    equivalentTerm :: Term
  } deriving (Eq, Ord, Show)

type Subst = Map.Map T.Text Term

matchETerm :: ETerm -> Term -> Maybe Subst
matchETerm p t = go p t Map.empty
  where
    go :: ETerm -> Term -> Subst -> Maybe Subst
    go (EVar v) t s =
      case Map.lookup v s of
        Nothing -> Just (Map.insert v t s)
        Just tOld -> if tOld == t then Just s else Nothing

    go (EOperation f ps) (Composed g as) s
      | f == g && length ps == length as =
          foldl step (Just s) (zip ps as)
      | otherwise = Nothing
      where
        step :: Maybe Subst -> (ETerm, Term) -> Maybe Subst
        step acc (p', a') = acc >>= \s' -> go p' a' s'
    go _ _ _ = Nothing

matchWithEquation :: Equation -> Term -> Maybe EquivalenceReceipt
matchWithEquation eq t =
  case (matchETerm (lhs eq) t, matchETerm (rhs eq) t) of
    (Nothing, Nothing) -> Nothing
    (Just sL, _) -> do
      t' <- applySubst sL (rhs eq)
      if t' == t 
        then Nothing
        else
          Just EquivalenceReceipt
                { term = t
                , equation = eq
                , matchesLhs = True
                , matchesRhs = False
                , equivalentTerm = t'
                }
    (Nothing, Just sR) -> do
      t' <- applySubst sR (lhs eq)
      if t' == t
        then Nothing
        else 
          Just EquivalenceReceipt
                { term = t
                , equation = eq
                , matchesLhs = False
                , matchesRhs = True
                , equivalentTerm = t'
                }

applySubst :: Map.Map T.Text Term -> ETerm -> Maybe Term
applySubst s (EVar v) = Map.lookup v s
applySubst s (EOperation f ts) = Composed f <$> traverse (applySubst s) ts



----------------------------
--- Recipe 
----------------------------


composeViaEquivalenceClassSet :: Map.Map SVariable Term -> Term -> Set.Set SRecipe
composeViaEquivalenceClassSet frame term =
  let reps :: Set.Set Term
      reps = Set.fromList (findEquivalenceClass [] term)
  in Set.fromList
       [ RVariable x
       | (x, v) <- Map.toList frame
       , v `Set.member` reps
       ]