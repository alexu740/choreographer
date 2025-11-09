{-# LANGUAGE OverloadedStrings #-}
module Choreography.State where

import Types.Simple (Constructors)

import Types.ChoreographyProtocolShell (RoleKnowledge (..))
import Types.Rewrite ( RewriteRules, RewriteTerm(..), RewriteVar(..), State(..), Check, Frame, Checks)
import Types.LocalBehavior (Label(..), Recipe (..))

import qualified Types.Rewrite as RRT
import qualified Types.Choreography as C
import qualified Choreography.Frame as Frame

import Syntax.Util (toText)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T

mkState :: RoleKnowledge -> State
mkState roleK =
  State
    { frame = Frame.initFrame (bounded roleK),
      unboundedTerms = unbounded roleK,
      boundedRecipes = Set.empty,
      prevDestructed = Set.empty,
      prevChecks = [],
      sessionID = Nothing
    }

insertFrame :: Label -> C.Term -> State -> State
insertFrame l t state =
  state {frame = Map.insert l t $ frame state}

insertDestruction :: Label -> State -> State
insertDestruction l state =
  state {prevDestructed = Set.insert l $ prevDestructed state}

insertDestructions :: Set.Set Label -> State -> State
insertDestructions ls state =
  state {prevDestructed = Set.union ls (prevDestructed state)}

insertCheck :: Check -> State -> State
insertCheck c state =
  state {prevChecks = c : prevChecks state}

insertChecks :: Checks -> State -> State
insertChecks cs state =
  state {prevChecks = cs ++ prevChecks state}

boundUnbounded :: Frame -> RRT.RewriteTerm -> Maybe (Recipe, C.Term)
boundUnbounded _ (RRT.Atom v) = return (LAtom v, C.Atomic v)
boundUnbounded fr (RRT.Comp f subterms) = do
  subterms' <- traverse (boundUnbounded fr) subterms
  let (rs, ts) = unzip subterms'
  return (LComp f rs, C.Composed f ts)
boundUnbounded fr (RRT.RewriteVar v) =
  case Map.toList $ Map.filterWithKey (\_ x -> x == C.Atomic v') fr of
    [] -> Nothing -- If no match, return Nothing
    ((l, t) : _) -> return (LAtom l, t) -- If multiple matches, return the first one
  where
    v' = rewriteVarToText v

boundUnboundedLs :: RewriteRules -> Constructors -> Frame -> [RRT.RewriteTerm] -> ([RRT.RewriteTerm], Set.Set (Recipe, C.Term))
boundUnboundedLs _ _ _ [] = ([], Set.empty)
boundUnboundedLs rules constructors fr (x : xs) =
  case boundUnbounded fr x of
    Nothing -> (x : xs', ys)
    Just (r, t) -> (xs', Set.insert (r, t) ys)
  where
    (xs', ys) = boundUnboundedLs rules constructors fr xs

updateUnboundedTerms :: RewriteRules -> Constructors -> State -> State
updateUnboundedTerms rules constructors state =
  state {unboundedTerms = unboundedTerms', boundedRecipes = boundedRecipes state `Set.union` boundedRecipes'}
  where
    (unboundedTerms', boundedRecipes') = boundUnboundedLs rules constructors (frame state) (unboundedTerms state)

addSessionID :: Maybe C.Term -> State -> State
addSessionID sid state =
  case sessionID state of
    Just _ -> state -- If session ID already exists, do not overwrite
    Nothing -> state {sessionID = sid}
    
rewriteVarToText :: RewriteVar -> T.Text
rewriteVarToText KEY = T.pack "key"
rewriteVarToText MSG = T.pack "msg"
rewriteVarToText RANDOM = T.pack "random"
rewriteVarToText PAIR1 = T.pack "pair1"
rewriteVarToText PAIR2 = T.pack "pair2"
rewriteVarToText (UnDef v) = v

rewriteTermToText :: RewriteTerm -> T.Text
rewriteTermToText (RewriteVar v) = rewriteVarToText v
rewriteTermToText (Atom v) = v
rewriteTermToText (Comp f args) =
  T.concat
    [ toText f,
      "(",
      T.intercalate "," (map rewriteTermToText args),
      ")"
    ]