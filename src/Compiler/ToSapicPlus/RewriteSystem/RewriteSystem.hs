{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.RewriteSystem.RewriteSystem where

import Types.Simple (FUNCTIONS(..), Function)
import Types.Sapic(Rule, SConstructors, SapicTranslationError, BuiltinTheory(..))
import Compiler.ToSapicPlus.RewriteSystem.Rule(getAllRules, constructorsStd)
import Types.ChoreographyProtocolShell (ProtocolDescription(..), RoleInfo(..), Sigma(..), Knowledge)
import Types.Choreography (Choreography(..), Atomic(..), Term(..))

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Char (toLower)

data RewriteSystem
  = RewriteSystem
  { systemRules :: [Rule],
    systemConstructors :: SConstructors
  } deriving (Eq, Show)

initializeRewriteSystem :: ProtocolDescription -> Either SapicTranslationError RewriteSystem
initializeRewriteSystem description = do
  let notOverwrittenDefaultFunctions = checkDefinedFunctions description
  if notOverwrittenDefaultFunctions
  then Right (getRewriteSystem description)
  else Left (T.pack "Redefining builtins is not allowed: " <> T.pack (show constructorsStd))
    

getRewriteSystem :: ProtocolDescription -> RewriteSystem
getRewriteSystem description = do
  let sigma = protocolSigma description
  RewriteSystem {
    systemRules = getAllRules description,
    systemConstructors = buildConstructors sigma constructorsStd
  }
  where
    buildConstructors :: Sigma -> Map.Map FUNCTIONS Int -> Map.Map FUNCTIONS Int
    buildConstructors sigma constructorsStd =
      constructorsStd `Map.union` Map.mapKeysMonotonic UnDef (Map.union (public sigma) (private sigma))

checkDefinedFunctions :: ProtocolDescription -> Bool
checkDefinedFunctions description = do
  let sigma = protocolSigma description
  let funct = Map.union (public sigma) (private sigma)
  all (notBuiltIn builtinSet) (Map.toList funct)
  where
    builtinSet :: Set.Set (T.Text, Int)
    builtinSet = Set.fromList
      [ (lowerShow f, ar) | (f, ar) <- Map.toList constructorsStd ]

    notBuiltIn :: Set.Set (T.Text, Int) -> (T.Text, Int) -> Bool
    notBuiltIn builtins (name, ar) = (T.toLower name, ar) `Set.notMember` builtins

    lowerShow :: FUNCTIONS -> T.Text
    lowerShow = T.toLower . T.pack . show


---- Find all unique function symbols used in choreography ----
collectChoreo :: Choreography -> [T.Text]
collectChoreo Nil = []
collectChoreo (Lock _ a) = collectAtomic a
collectChoreo (Interaction _ _ pairs _def) =
  concatMap (\(t,c) -> collectTerm t ++ collectChoreo c) pairs

funText :: Function -> T.Text
funText = T.toLower . T.pack . show

collectTerm :: Term -> [T.Text]
collectTerm (Atomic _) = []
collectTerm (Composed f args) = funText f : concatMap collectTerm args

collectAtomic :: Atomic -> [T.Text]
collectAtomic (Nonce _ a) = collectAtomic a
collectAtomic (Read _ _ t a) = collectTerm t ++ collectAtomic a ++ collectTerm (Composed CELL [t, t])
collectAtomic (Write _ t1 t2 a) = collectTerm t1 ++ collectTerm t2 ++ collectAtomic a ++ collectTerm (Composed CELL [t1, t2])
collectAtomic (If t1 t2 a1 a2) = collectTerm t1 ++ collectTerm t2 ++ collectAtomic a1 ++ collectAtomic a2
collectAtomic (Choice _ _ _ a) = collectAtomic a
collectAtomic (Release _ _ a) = collectAtomic a
collectAtomic (Unlock c) = collectChoreo c


uniq :: Ord a => [a] -> [a]
uniq = go Set.empty
  where
    go _ [] = []
    go seen (x:xs) | x `Set.member` seen = go seen xs
                   | otherwise = x : go (Set.insert x seen) xs

collectFunctionSymbols :: Choreography -> [T.Text]
collectFunctionSymbols = uniq . collectChoreo

-------------------------------------------
----- Deduce theories ----

deduceTheories :: ProtocolDescription -> [BuiltinTheory]
deduceTheories description = do
  let syms = collectFunctionSymbols (protocolChoreo description)
  let s = Set.fromList (map T.toLower syms)
      anyOf = any (`Set.member` s)
  [ t
      | (t, used) <-
          [ (Hashing, anyOf ["h","hash"])
          , (AsymmetricEncryption, anyOf ["aenc","adec"])
          , (Signing, anyOf ["sign","verify"])
          , (RevealingSigning, anyOf ["revealsign","revealverify","getmessage"])
          , (SymmetricEncryption, anyOf ["senc","sdec"])
          , (DiffieHellman, anyOf ["mult","exp"])
          ]
      , used
    ]