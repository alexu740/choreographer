-- SPDX-FileCopyrightText: 2023 Technical University of Denmark
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- From the noname-tool, updated to noname+

-- {-# LANGUAGE OverloadedStrings #-}

module Compiler.ToNoname.Noname.Syntax where

-- text
import Data.Text (Text)

-- import qualified Data.Text as Text

-- | A term is either atomic or composed with subterms.
data Term a b
  = -- | Atomic term.
    Atom b
  | -- | Composed term.
    Comp a [Term a b]
  deriving (Eq, Ord, Show)

-- | Representation of identifiers.
type Identifier = Text

-- | Variable names.
type Variable = Identifier

-- | Function names.
type Function = Identifier

-- | Relation names.
type Relation = Identifier

-- | Cell names.
type Cell = Identifier

-- | A label is a special identifier for messages in the intruder knowledge.
type Label = Identifier

-- | A message is a term using privacy and intruder variables and functions.
type Message = Term Function Variable

-- | A domain is a list of constants (functions of arity 0).
type Domain = [Function]

-- | A quantifier-free FOL formula.
data Formula
  = -- | Trivially true formula.
    Top
  | -- | Equality between messages.
    Equality Message Message
  | -- | Relation over messages.
    Relational Relation [Message]
  | -- | Negation.
    Neg Formula
  | -- | Conjunction.
    And Formula Formula
  deriving (Eq, Show)

-- | Mode for non-deterministic choices of variables.
data Mode
  = -- | The mode \(\star\) for \(\alpha\)-variables.
    Star
  | -- | The mode \(\diamond\) for \(\beta\)-variables.
    Diamond
  deriving (Eq, Show)

-- | A left process is the first part in a transaction.
data LeftProcess
  = -- | Non-deterministic choice of variable.
    Choice Mode Variable Domain LeftProcess
  | -- | Receive a message.
    Receive Variable LeftProcess
  | -- | Continue with a center process.
    Center CenterProcess
  deriving (Eq, Show)

--  Let expression binding.
--  LetLeft Variable Message LeftProcess

-- | A center process is after a left process and before a right process.
data CenterProcess
  = -- | Destructor application.
    Try Variable Function [Message] CenterProcess CenterProcess
  | -- | Cell read.
    Read Variable Cell Message CenterProcess
  | -- | Conditional statement.
    If Formula CenterProcess CenterProcess
  | -- | Fresh constants.
    New [Variable] RightProcess
  deriving (Eq, Show)

-- Let expression binding.
-- LetCenter Variable Message CenterProcess

-- | A right process is the last part in a transaction.
data RightProcess
  = -- | Send a message.
    Send Message RightProcess
  | -- | Cell write.
    Write Cell Message Message RightProcess
  | -- | Release a formula in \(\alpha\) (releases in \(\beta\) not supported).
    Release Mode Formula RightProcess
  | -- | Terminate with the nil process.
    Nil
  | -- | Sequence.
    Sequence LeftProcess
  deriving (Eq, Show)

--  Let expression binding.
--  LetRight Variable Message RightProcess

-- | A process is a left, center or right process.
data Process
  = -- | Left process.
    Pl LeftProcess
  | -- | Center process.
    Pc CenterProcess
  | -- | Right process.
    Pr RightProcess
  deriving (Eq, Show)
