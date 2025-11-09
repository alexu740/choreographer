{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.InitialKnowledgeDistributor where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Text as T
import Types.Simple (FUNCTIONS(..), Function)
import Types.Choreography
import Types.ChoreographyProtocolShell
import Types.Sapic(SapicTranslationError, Rule(..))


getDependantRolesFromKnowledge :: Agent -> [Term] -> ProtocolDescription -> Either SapicTranslationError [Agent]
getDependantRolesFromKnowledge agent initialTerms description =
  let allAgents = Map.keysSet (protocolRoles description)
      atomics = concatMap collectAtomics initialTerms
      uniqueAtoms = uniqPreserveOrder atomics
      nonAgents = filter (`Set.notMember` allAgents) uniqueAtoms
  in case nonAgents of
       [] -> Right (removeItem agent uniqueAtoms)
       na ->
         Left $
           "Only agent variables are allowed in initial knowledge. "
           <> "Following are not agent variables: "
           <> T.intercalate ", " na

collectAtomics :: Term -> [Agent]
collectAtomics (Atomic a) = [a]
collectAtomics (Composed _ ts) = concatMap collectAtomics ts

-- | Dedupe but keep the same order
uniqPreserveOrder :: (Ord a) => [a] -> [a]
uniqPreserveOrder = go Set.empty
  where
    go _ [] = []
    go seen (x:xs)
      | x `Set.member` seen = go seen xs
      | otherwise = x : go (Set.insert x seen) xs

removeItem :: Eq a => a -> [a] -> [a]
removeItem x = filter (/= x)