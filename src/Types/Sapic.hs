{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Types.Sapic where

import qualified Data.Text as T
import qualified Data.Map as Map
import Types.Simple (FUNCTIONS, Function)

type Symbol = T.Text

type SName = Symbol
type SVariable = Symbol

type SConstructors = Map.Map FUNCTIONS Int

-- T(F,N,X)
data STerm
  = TName SName
  | TVariable SVariable
  | TFunction Function [STerm]
  deriving (Eq, Ord, Show)

-- Recipes and checks --
type Check = (SRecipe, SRecipe)
data SRecipe
  = RVariable SVariable
  | RFunction Function [SRecipe]
  deriving (Eq, Ord, Show)
-----

-- Sapic process definition --
data SProcess
  = SNew STerm SProcess
  | SOut [(STerm, SProcess)]
  | SIn STerm SProcess
  | SIf STerm STerm SProcess SProcess
  | SLet SPattern STerm SProcess SProcess
  | SInsert STerm STerm SProcess
  | SLookup STerm SVariable SProcess SProcess
  | SLock SProcess
  | SUnlock SProcess
  | SNil
  | SReplication SProcess
  | SParallel [SProcess]
  | SAgentInitialisation Symbol [STerm]
  | SChoice STerm T.Text SProcess SProcess
  | SFact SFactType [SFactArgument] SProcess
  deriving (Eq, Show)

data SPattern
  = PData Function [SPatternArg]
  | PVar SVariable
  | PTerm STerm
  deriving (Eq, Show)

data SPatternArg
  = PBind STerm -- variable term!!
  | PCompare STerm
  deriving (Eq, Show)

data SFactType 
  = Secret 
  | Witness 
  | Request 
  | Honest
  | Dishonest
  deriving (Eq, Show)

type SFactConstant = T.Text

data SFactArgument
  = SFTerm STerm 
  | SFConst SFactConstant
  deriving (Eq, Show)



type SapicTranslationError = T.Text
-----

-- Final protocol shape --
data SProtocol = SProtocol 
  { protocolHeader :: SProtocolHeader,
    agentProcesses :: [SAgentProcess],
    mainProcess :: SProcess,
    lemmas :: [Lemma],
    queries :: [ProverifQuery]
  } deriving (Eq, Show)

type SProtocolHeaderFunction = (T.Text, Bool)

data BuiltinTheory
  = Hashing | AsymmetricEncryption | Signing | RevealingSigning | SymmetricEncryption | DiffieHellman
  deriving (Eq, Ord, Show)

data SProtocolHeader = SProtocolHeader {
    theory :: T.Text,
    builtins :: [BuiltinTheory],
    functions :: [SProtocolHeaderFunction],
    equations :: [Rule]
  } deriving (Eq, Show)

data SAgentProcess = SAgentProcess {
    processName :: Symbol,
    processHeader :: [Symbol],
    processBody :: SProcess
  } deriving (Eq, Show)

-- Lemma types --
data LFact
  = PSecret
  | PWitness
  | PRequest
  | PIntruderKnows
  | PHonest
  | PDishonest
  deriving (Eq, Ord, Show)

type Time = Symbol
  
data LFormula
  = FFact LFact [Symbol] Time
  | FNot LFormula
  | FAnd LFormula LFormula
  | FOr LFormula LFormula
  | FImply LFormula LFormula
  | FForall [T.Text] LFormula
  | FExists [T.Text] LFormula
  | FEq Symbol Symbol
  deriving (Eq, Ord, Show)

data Lemma = Lemma
  { lemmaName :: T.Text
  , output :: [LemmaOutput]
  , existsTrace :: Bool
  , lemmaBody :: LFormula
  } deriving (Eq, Show)

data LemmaOutput 
  = Spthy 
  | Proverif 
  | Empty  
  deriving (Eq, Show)

data ProverifQuery = ProverifQuery {
    arguments :: [(T.Text, T.Text)],
    query :: ProverifFormula
  } deriving (Eq, Show)

data ProverifFormula
  = PVEvent LFact [Symbol]
  | PVOr ProverifFormula ProverifFormula
  | PVInjEvent LFact [Symbol]
  | PVAnd ProverifFormula ProverifFormula
  | PVImpl ProverifFormula ProverifFormula
  deriving (Eq, Show)
-----

-- Rewrite rules --
data Rule = Rule
  { destructor :: Function
  , args :: [RTerm]
  , result :: RTerm
  } deriving (Eq, Show)

data RTerm
  = RVar T.Text
  | RConstr Function [RTerm]
  deriving (Eq, Show)
-----
