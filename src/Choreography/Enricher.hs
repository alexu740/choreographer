{-# LANGUAGE OverloadedStrings #-}

module Choreography.Enricher where

import qualified Types.Choreography as C
import qualified Types.Simple as F
import Types.Simple(Function, FUNCTIONS(..))
import Types.ChoreographyProtocolShell
import Types.Rewrite (RewriteRules, RewriteRule, Pattern, Replacement, RewriteTerm(..),
      RewriteVar(..))
import qualified Types.Rewrite as RR
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Map as Map
import qualified Data.Text as T
import Syntax.Util (getRoleChoices, toText)

import Debug.Trace (trace, traceShowId)

destructorRules :: C.Agent -> RewriteRules
destructorRules role =
  Map.fromList
    [ (F.UnDef $ destructorName role, ([constructor], RewriteVar (RR.UnDef "x"))),
      (F.UnDef $ rdestructorName role, ([constructor], RewriteVar (RR.UnDef "r")))
    ]
  where
    constructor =
      Comp
        (F.UnDef $ constructorName role)
        [ RewriteVar (RR.UnDef "x"),
          RewriteVar (RR.UnDef "r")
        ]

roleFunctions :: C.Agent -> Knowledge
roleFunctions role =
  Map.fromList
    [ (constructorName role, 2),
      (destructorName role, 1),
      (rdestructorName role, 1)
    ]

constructorName, destructorName, rdestructorName :: C.Agent -> T.Text
constructorName = T.append "init"
destructorName = T.append "dinit"
rdestructorName = T.append "rinit"

-- | All rewrite rules, combining destructor and verifier rules.
-- Each entry maps a function symbol (e.g., DSCRYPT) to a pattern and replacement.
stdRewriteRules :: RewriteRules
stdRewriteRules = stdRewriteRulesDestructors -- TODO: remove `Map.union` rewriteRulesVerifiers

-- | Rewrite rules for destructors (e.g., decryption, projection).
-- Match structured input and produce a subterm.
stdRewriteRulesDestructors :: RewriteRules
stdRewriteRulesDestructors =
  Map.fromList
    [ ( DSCRYPT,
        mkRule
          [ RewriteVar KEY,
            Comp SCRYPT [RewriteVar KEY, RewriteVar MSG, RewriteVar RANDOM]
          ]
          (RewriteVar MSG)
      ),
      ( DCRYPT,
        mkRule
          [ Comp INV [RewriteVar KEY],
            Comp CRYPT [RewriteVar KEY, RewriteVar MSG, RewriteVar RANDOM]
          ]
          (RewriteVar MSG)
      ),
      ( OPEN,
        mkRule
          [ RewriteVar KEY,
            Comp SIGN [Comp INV [RewriteVar KEY], RewriteVar MSG]
          ]
          (RewriteVar MSG)
      ),
      (PROJ1, mkRule [Comp PAIR [RewriteVar PAIR1, RewriteVar PAIR2]] (RewriteVar PAIR1)),
      (PROJ2, mkRule [Comp PAIR [RewriteVar PAIR1, RewriteVar PAIR2]] (RewriteVar PAIR2)),
      (PUBK, mkRule [Comp INV [RewriteVar KEY]] (RewriteVar KEY)),
      (SFST, mkRule [Comp SESSION [RewriteVar (RR.UnDef "x"), RewriteVar (RR.UnDef "y")]] (RewriteVar (RR.UnDef "x"))),
      (SSND, mkRule [Comp SESSION [RewriteVar (RR.UnDef "x"), RewriteVar (RR.UnDef "y")]] (RewriteVar (RR.UnDef "y"))),
      (DSID, mkRule [Comp SID [RewriteVar (RR.UnDef "id")]] (RewriteVar (RR.UnDef "id")))
    ]

mkRule :: Pattern -> Replacement -> RewriteRule
mkRule = (,)