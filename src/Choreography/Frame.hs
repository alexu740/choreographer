{-# LANGUAGE OverloadedStrings #-}

module Choreography.Frame where

import Types.Simple ( Constructors, FUNCTIONS (UnDef))
import Types.LocalBehavior (Label, Recipe (..))
import Types.Choreography (Term(..))
import Types.Rewrite (Binding, RewriteRules, RewriteTerm(..), RewriteVar, FrameError(..), Frame)

import Syntax.Util (top)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T

-- | Initialize a frame from a list of terms, assigning them labels like X0, X1, ...
initFrame :: [Term] -> Frame
initFrame ts =
  Map.fromList $ labels `zip` ts
  where
    labels = map (\i -> "X" <> T.pack (show (i :: Int))) [0 ..]

-- | Creates a new label index for a list of state-atomic pairs.
-- The new index is the length of the longest frame.
newIndex :: [Frame] -> Int
newIndex frames =
  maximum $ map (length . Map.keys) frames

-- | Creates a new label for a list of state-atomic pairs.
-- The new label is Xi where i is the length of the longest frame.
newLabel :: [Frame] -> Label
newLabel frames =
  "X" `T.append` (T.pack . show $ newIndex frames)

newLabels :: Int -> [Frame] -> [Label]
newLabels n frames =
  let index = newIndex frames
   in map (\i -> "X" `T.append` (T.pack . show $ index + i)) [0 .. n - 1]

-- | Apply a frame to a local recipe to produce a term.
-- If the recipe has a destructor or verifier, rewrite rules are used.
applyFrame :: RewriteRules -> Constructors -> Frame -> Recipe -> Either FrameError Term
applyFrame rules constructors frame recipe =
  case recipe of
    LAtom l
      | l == top -> return (Atomic top)
      | Just t <- Map.lookup l frame -> return t
      | Just arity <- Map.lookup (UnDef l) constructors,
        arity == 0 ->
          return (Atomic l)
      | otherwise -> Left $ UndefinedLabel (frame, l)
    LComp f rs -> do
      rs' <- traverse (applyFrame rules constructors frame) rs
      case Map.lookup f rules of
        Nothing -> return (Composed f rs')
        Just rewrite -> do
          binding <- matchPattern (fst rewrite) rs'
          applyBinding binding (snd rewrite)

-- | Match a list of rewrite terms against a list of actual terms,
-- producing a binding from rewrite variables to concrete terms if successful.
matchPattern :: [RewriteTerm] -> [Term] -> Either FrameError Binding
matchPattern [] [] = return Map.empty
matchPattern (rewriteTerm : rts) (term : ts) = do
  bindingterm <- matchPatternSingle rewriteTerm term
  bindingrts <- matchPattern rts ts
  bindingterm `mergeBindings` bindingrts
matchPattern _ _ = Left NonMatchingPattern

-- | Match a single rewrite term to a concrete term, producing a partial binding.
matchPatternSingle :: RewriteTerm -> Term -> Either FrameError Binding
matchPatternSingle (RewriteVar c) term = return (Map.singleton c term)
matchPatternSingle (Atom var) (Atomic var')
  | var == var' = return Map.empty
matchPatternSingle (Comp f args) (Composed f' args')
  | f == f' = matchPattern args args'
matchPatternSingle _ _ = Left NonMatchingPattern

-- | Merge two bindings, ensuring that overlapping keys are bound to equal terms.
mergeBindings :: Binding -> Binding -> Either FrameError Binding
mergeBindings b1 b2 =
  if all consistent (Map.keysSet b1 `Set.intersection` Map.keysSet b2)
    then return (Map.union b1 b2)
    else Left NonMergeableBindings
  where
    consistent k = Map.lookup k b1 == Map.lookup k b2

-- | Apply a substitution binding to a rewrite term, producing a concrete term.
applyBinding :: Binding -> RewriteTerm -> Either FrameError Term
applyBinding binding (RewriteVar c) =
  maybe (Left (UndefinedRewriteVar c)) Right $
    Map.lookup c binding
applyBinding _ (Atom var) = return (Atomic var)
applyBinding binding (Comp f args) = do
  args' <- traverse (applyBinding binding) args
  return $ Composed f args'