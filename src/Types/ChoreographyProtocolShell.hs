module Types.ChoreographyProtocolShell where

import Types.Simple (Cell, Identifier, Mode)
import Types.Choreography (Agent, Choreography, Term)
import Types.LocalBehavior (Domain) -- problematic
import Types.Rewrite (RewriteRules, RewriteTerm)

import qualified Data.Map as Map

data ProtocolDescription
  = ProtocolDescription
  { protocolSigma0 :: Sigma,
    protocolSigma :: Sigma,
    protocolAlgebra :: RewriteRules,
    protocolCells :: InitCells,
    protocolRoles :: Roles,
    protocolChoreo :: Choreography,
    protocolGoals :: [SecurityGoal]
  }
  deriving (Show, Eq)

data SecurityGoal 
  = Secrecy Term [Agent] 
  | WeakAuth Agent Agent Term
  | StrongAuth Agent Agent Term
  deriving (Show, Eq)

data Sigma
  = Sigma
  { public :: Knowledge,
    private :: Knowledge,
    relation :: Knowledge
  }
  deriving (Show, Eq)

type Roles = Map.Map Agent RoleInfo
type Knowledge = Map.Map Identifier Int
type InitCells = Map.Map Cell (Term, Term)

data RoleInfo
  = RoleInfo
  { roleKnowledge :: [Term],
    roleChoice :: Maybe (Mode, Domain)
  }
  deriving (Show, Eq)

data RoleKnowledge
  = RoleKnowledge
  { 
    bounded :: [Term],
    unbounded :: [RewriteTerm]
  }