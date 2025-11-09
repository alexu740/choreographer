{-# LANGUAGE OverloadedStrings #-}
module Compiler.ToSapicPlus.RewriteSystem.Rule where

import Types.Simple (Function, FUNCTIONS(..))
import Types.Rewrite (RewriteRules, RewriteRule(..), RewriteTerm(..))
import qualified Types.Rewrite as RW
import Types.Sapic(SConstructors, Rule(..), RTerm(..))
import Data.Text (Text)
import qualified Data.Map as Map
import qualified Data.Text as T
import Types.ChoreographyProtocolShell (ProtocolDescription(..) )

-- these are only usable in initial knowledge definitions
-- will be diplayed as functions in the printed version of the translation
specialConstructors :: SConstructors
specialConstructors = Map.fromList [(PRIV, 1), (SK, 2)]

constructorsStd :: SConstructors
constructorsStd = Map.fromList [
  -- Sapic specific
  (H, 1), (AENC, 2), (SENC, 2), (SIGN, 2), (REVEALSIGN, 2), (CELL, 2), (PK, 1), (PAIR, 2), (UnDef "true", 0), (G, 0)
  
  -- Original
  ]

rules :: [Rule]
rules =
  [ 
     Rule {
      destructor = ADEC
      , args =
          [ 
            RConstr AENC [ RVar "MSG", RConstr PK [RVar "KEY"] ],
            RVar "KEY"
          ]
      , result = RVar "MSG"
    }

  , Rule {
      destructor = SDEC
      , args =
          [ 
            RConstr SENC [ RVar "MSG", RVar "KEY" ],
            RVar "KEY"
          ]
      , result = RVar "MSG"
    },

    -- PROJ1: proj1(pair(PAIR1, PAIR2)) = PAIR1
    Rule
      { destructor = PROJ1
      , args = [ RConstr PAIR [ RVar "PAIR1", RVar "PAIR2" ] ]
      , result = RVar "PAIR1"
      }

    -- PROJ2: proj2(pair(PAIR1, PAIR2)) = PAIR2
  , Rule
      { destructor = PROJ2
      , args = [ RConstr PAIR [ RVar "PAIR1", RVar "PAIR2" ] ]
      , result = RVar "PAIR2"
      }

  -- getMessage(revealSign(m,sk)) = m
  , Rule
      { destructor = GETMESSAGE
      , args =
          [ 
            RConstr REVEALSIGN [ RVar "MSG", RVar "KEY" ]
          ]
      , result = RVar "MSG"
      },

-------------- old, not to be used
    -- DSCRYPT: sdec(senc(MSG, KEY, RANDOM), KEY) = MSG
    Rule
      { destructor = DSCRYPT
      , args =
          [ 
            RVar "KEY",
            RConstr SCRYPT [ RVar "KEY", RVar "MSG", RVar "RANDOM" ]
          ]
      , result = RVar "MSG"
      }

    -- DCRYPT: dcrypt(inv(KEY), crypt(KEY, MSG, RANDOM)) = MSG
  , Rule
      { destructor = DCRYPT
      , args =
          [ RConstr INV  [ RVar "KEY" ]
          , RConstr CRYPT [ RVar "KEY", RVar "MSG", RVar "RANDOM" ]
          ]
      , result = RVar "MSG"
      }
------------
    -- OPEN: open(KEY, sign(inv(KEY), MSG)) = MSG
  , Rule
      { destructor = OPEN
      , args =
          [ RVar "KEY"
          , RConstr SIGN [ RConstr INV [ RVar "KEY" ], RVar "MSG" ]
          ]
      , result = RVar "MSG"
      }
    -- SFST: sfst(session(x, y)) = x
  , Rule
      { destructor = SFST
      , args = [ RConstr SESSION [ RVar "x", RVar "y" ] ]
      , result = RVar "x"
      }

    -- SSND: ssnd(session(x, y)) = y
  , Rule
      { destructor = SSND
      , args = [ RConstr SESSION [ RVar "x", RVar "y" ] ]
      , result = RVar "y"
      }

    -- DSID: dsid(sid(id)) = id
  , Rule
      { destructor = DSID
      , args = [ RConstr SID [ RVar "id" ] ]
      , result = RVar "id"
      }
  ]

verifierRules :: [Rule]
verifierRules = [
  -- revealVerify(revealSign(m,sk),m,pk(sk)) = true
-- verify(sign(m,sk),m,pk(sk)) = true
    Rule
      { destructor = REVEALVERIFY
      , args =
          [ 
            RConstr REVEALSIGN [ RVar "MSG", RVar "KEY" ],
            RVar "MSG",
            RConstr PK [RVar "KEY"]
          ]
      , result = RConstr (UnDef "true") []
      },
      Rule
      { destructor = VERIFY
      , args =
          [ 
            RConstr SIGN [ RVar "MSG", RVar "KEY" ],
            RVar "MSG",
            RConstr PK [RVar "KEY"]
          ]
      , result = RConstr (UnDef "true") []
      }
  ]


-- Get combined rules ---
getUserDefinedRules :: ProtocolDescription -> [Rule]
getUserDefinedRules description =
  let defRules = protocolAlgebra description
  in map toSRule (Map.toList defRules)

getAllRules :: ProtocolDescription -> [Rule]
getAllRules description = rules ++ getUserDefinedRules description

----
toSRule :: (Function, RewriteRule) -> Rule
toSRule (f, (pat, rhs)) =
  Rule { destructor = f
  , args = map toRTerm pat
  , result = toRTerm rhs
  }

toRTerm :: RewriteTerm -> RTerm
toRTerm rt = case rt of
  Atom v -> RVar v
  RewriteVar (RW.UnDef v) -> RVar v
  RewriteVar v -> RVar (T.pack (show v))
  Comp g ts -> RConstr g (map toRTerm ts)
----