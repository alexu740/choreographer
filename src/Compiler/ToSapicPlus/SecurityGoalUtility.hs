{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToSapicPlus.SecurityGoalUtility where

import Types.Simple(Function)
import Types.Sapic (LemmaOutput(..), Symbol, SapicTranslationError, SProcess(..), STerm(..), SFactType(..), Lemma(..), LFormula(..), Time, LFact(..), SFactArgument(..), ProverifQuery(..), ProverifFormula (..) )
import Types.ChoreographyProtocolShell (ProtocolDescription(..), SecurityGoal(..))
import Types.Choreography (Agent, Term(..))

import Compiler.ToSapicPlus.SFrame (SFrame, toNameBasedSTerm, choreoTermToSTerm)
import Compiler.ToSapicPlus.RecipeUtility (compose)

import qualified Data.Text as T

applyGoalsAtEndOfProtocol :: ProtocolDescription -> Agent -> [SFrame] -> SProcess
applyGoalsAtEndOfProtocol description agent frames =
  let authGoals =
        [ ("WeakAuth",  t, a1, a2) | WeakAuth a1 a2 t <- protocolGoals description
                                   , a1 == agent, composable t ] ++
        [ ("StrongAuth", t, a1, a2) | StrongAuth a1 a2 t <- protocolGoals description
                                    , a1 == agent, composable t ]
      requestFacts = map mkRequest authGoals
      cont = applySecrecy description agent frames
      chained = foldr (SFact Request) cont requestFacts
      anyRelevantGoals = not (null authGoals)
  in if anyRelevantGoals then SNew (TName "sid") chained else chained
  where
    composable t = all (`hasRecipe` t) frames
    hasRecipe fr t = case compose description fr t of { Just _ -> True; Nothing -> False }
    toSTerm t = case frames of 
        (fr:_) -> toNameBasedSTerm fr (choreoTermToSTerm t)
        [] -> choreoTermToSTerm t
    mkRequest (tag,t,a1,a2) =
      let base = [ SFTerm $ TName a1, SFTerm $ TName a2, SFConst (goalId (tag, t, a1, a2)), SFTerm $ toSTerm t ]
      in base ++ [SFTerm $ TName "sid"]

applySecrecy :: ProtocolDescription -> Agent -> [SFrame] -> SProcess
applySecrecy description agent frames =
  case facts of
    [] -> SNil
    _ -> chainFacts facts
  where
    goals :: [(Term, [Agent])]
    goals =
      [ (t, agents) | Secrecy t agents <- protocolGoals description, agent `elem` agents ]

    facts :: [(SFactArgument, [Agent])]
    facts =
      [ (SFTerm st, agents) | (term, agents) <- goals, frame  <- frames, let st = toNameBasedSTerm frame (choreoTermToSTerm term), hasRecipe frame term ]

    hasRecipe :: SFrame -> Term -> Bool
    hasRecipe frame term = do
      let result = compose description frame term
      case result of
        Just _ -> True
        Nothing -> False

    chainFacts :: [(SFactArgument, [Agent])] -> SProcess
    chainFacts [] = SNil
    chainFacts ((term, agents):t) = SFact Secret (term : agentsToTerm agents) (chainFacts t)

    agentsToTerm :: [Agent] -> [SFactArgument]
    agentsToTerm [] = []
    agentsToTerm (a:rest) = SFTerm (TVariable a) : agentsToTerm rest

pruneAuthenticationGoalsFromDescription
  :: ProtocolDescription -> Agent -> [SFrame] -> ProtocolDescription
pruneAuthenticationGoalsFromDescription description agent frames =
  description { protocolGoals = filter (not . applicable) (protocolGoals description) }
  where
    applicable :: SecurityGoal -> Bool
    applicable (WeakAuth _ b t) = b == agent && composable t
    applicable (StrongAuth _ b t) = b == agent && composable t
    applicable _ = False

    composable :: Term -> Bool
    composable t = all (`hasRecipe` t) frames

    hasRecipe :: SFrame -> Term -> Bool
    hasRecipe fr t = case compose description fr t of
        Just _ -> True
        Nothing -> False

applyWitnessEventsFromGoals :: ProtocolDescription -> Agent -> [SFrame] -> Either SapicTranslationError SProcess -> Either SapicTranslationError SProcess
applyWitnessEventsFromGoals description agent frames cont0 =
  case cont0 of
    Left e -> Left e
    Right p0 ->
      let goals = [ ("WeakAuth", t, a1, a2)
                    | WeakAuth a1 a2 t <- protocolGoals description, a2 == agent, composable t
                  ] ++
                  [ ("StrongAuth", t, a1, a2)
                    | StrongAuth a1 a2 t <- protocolGoals description, a2 == agent, composable t
                  ]
                  
          events = map mkWitness goals
      in Right (foldr (SFact Witness) p0 events)
  where
    composable :: Term -> Bool
    composable t = all (`hasRecipe` t) frames

    mkWitness :: (T.Text, Term, Agent, Agent) -> [SFactArgument]
    mkWitness (g, t, a1, a2) =
      [ SFTerm $ TName a2
      , SFTerm $ TName a1
      , SFConst (goalId (g, t, a1, a2))
      , SFTerm $ toSTerm t 
      ]

    toSTerm :: Term -> STerm
    toSTerm t = case frames of
      (fr:_) -> toNameBasedSTerm fr (choreoTermToSTerm t)
      [] -> choreoTermToSTerm t

    hasRecipe :: SFrame -> Term -> Bool
    hasRecipe fr t = case compose description fr t of
        Just _ -> True
        Nothing -> False

------
goalId :: (T.Text, Term, Agent, Agent) -> T.Text
goalId (kind, t, a1, a2) =
    kind <> a1 <> a2 <> termStamp t

termStamp :: Term -> T.Text
termStamp (Atomic v) = "Atomic" <> v
termStamp (Composed f args) = funToText f <> T.concat (map termStamp args)

funToText :: Function -> T.Text
funToText = T.pack . show

----- compose lemmas for printing
convertSecurityGoalsToLemms :: ProtocolDescription -> [Lemma]
convertSecurityGoalsToLemms description =
    map mkSec secGoals
 ++ map mkWeak weakGoals
 ++ map mkStr strongGoals
  where
    goals = protocolGoals description

    secGoals :: [(Term, [Agent])]
    secGoals = [ (t, as) | Secrecy t as <- goals ]

    weakGoals :: [(Term, Agent, Agent, T.Text)]
    weakGoals = [ (t, a1, a2, goalId ("WeakAuth", t, a1, a2)) | WeakAuth a1 a2 t <- goals ]

    strongGoals :: [(Term, Agent, Agent, T.Text)]
    strongGoals = [ (t, a1, a2, goalId ("StrongAuth", t, a1, a2)) | StrongAuth a1 a2 t <- goals ]

    xVar, iVar, jVar, tVar, sidVar :: Symbol
    xVar = "x"
    iVar = "#i"
    timeVar = "#ag"
    jVar = "#j"
    tVar = "t"
    sidVar = "sid"

    mkSec :: (Term, [Agent]) -> Lemma
    mkSec (_t, as) =
      let name = T.intercalate "_" (["secrecy"] ++ as ++ [termId _t])
          agentTimeVars = [ timeVar <> a | a <- as]
          body =
            FForall (as ++ [xVar, iVar] ++ agentTimeVars) (
              foldr (.&&.) (FFact PSecret (xVar : as) iVar) [ FFact PHonest [a] (timeVar <> a) | a <- as ] .==>. FNot (FExists [jVar] (FFact PIntruderKnows [xVar] jVar))
            )
      in Lemma name [Spthy]False body

    mkWeak :: (Term, Agent, Agent, T.Text) -> Lemma
    mkWeak (_t, a1, a2, gid) =
      let name = "weakAuth_" <> a1 <> "_" <> a2 <> "_" <> termId _t
          body =
            FForall [a1, a2, tVar, iVar, sidVar, timeVar] $
              (
                FFact PHonest [a1] timeVar .&&. 
                FFact PRequest [a2, a1, gid, tVar, sidVar] iVar
              ) .==>. FExists [jVar] (FFact PWitness [a1, a2, gid, tVar] jVar)
      in Lemma name [Spthy,Proverif]False body

    mkStr :: (Term, Agent, Agent, T.Text) -> Lemma
    mkStr (tGoal, a1, a2, gid) =
        let name = "strongAuth_" <> a1 <> "_" <> a2 <> "_" <> termId tGoal
            body = 
              FForall [a1, a2, tVar, iVar, sidVar, timeVar]
              (
                (
                  FFact PHonest [a1] timeVar .&&.
                  FFact PRequest [a2, a1, gid, tVar, sidVar] iVar
                ) 
                .==>. FExists [jVar]
                (
                  FFact PWitness [a1, a2, gid, tVar] jVar .&&.
                  FNot (
                    FExists [i1Var, i2Var, sidVar1, sidVar2]
                    (
                      FFact PRequest [a2, a1, gid, tVar, sidVar1] i1Var .&&.
                      FFact PRequest [a2, a1, gid, tVar, sidVar2] i2Var .&&.
                      FNot (FEq sidVar1 sidVar2)
                    )
                  )
                )
              )

        in Lemma name [Spthy] False body
        where 
            iVar, jVar, i1Var, i2Var, sidVar1, sidVar2, tVar :: Symbol
            iVar = "#i"
            jVar = "#j"
            i1Var = "#i1"
            i2Var = "#i2"
            sidVar1 = "sid1"
            sidVar2 = "sid2"
            tVar = "t"
      
    termId :: Term -> T.Text
    termId (Atomic v) = v
    termId (Composed f []) = T.pack (show f)
    termId (Composed f ts) = T.pack (show f) <> T.concat (map termId ts)

    (.==>.) = FImply
    (.&&.) = FAnd

convertSecurityGoalsToProverifQueries :: ProtocolDescription -> [ProverifQuery]
convertSecurityGoalsToProverifQueries description = 
   map mkSec secGoals
   ++ map mkStr strongGoals
 where
  goals = protocolGoals description

  secGoals :: [(Term, [Agent])]
  secGoals = [ (t, as) | Secrecy t as <- goals ]

  strongGoals :: [(Term, Agent, Agent, T.Text)]
  strongGoals = [ (t, a1, a2, goalId ("StrongAuth", t, a1, a2)) | StrongAuth a1 a2 t <- goals ]

  mkSec :: (Term, [Agent]) -> ProverifQuery
  mkSec (t, as) =
    let xVar = "x" :: Symbol
        args = (xVar, "bitstring") : [(a, "bitstring") | a <- as]
        dishonestDisj :: ProverifFormula
        dishonestDisj =
          case as of
            a:rs -> foldl
                      PVOr
                      (PVEvent PDishonest [a])
                      [ PVEvent PDishonest [b] | b <- rs ]
        lhs :: ProverifFormula
        lhs = PVAnd (PVEvent PSecret (xVar : as)) (PVEvent PIntruderKnows [xVar])

        body :: ProverifFormula
        body = PVImpl lhs dishonestDisj
    in ProverifQuery { arguments = args, query = body }

  mkStr :: (Term, Agent, Agent, T.Text) -> ProverifQuery
  mkStr (_tGoal, a1, a2, gid) =
    let sid = "sid" :: Symbol
        t   = "t" :: Symbol

        args :: [(T.Text, T.Text)]
        args =
          [ (a1 , "bitstring") 
          , (a2 , "bitstring")
          , (sid, "bitstring")
          , (t  , "bitstring")
          ]

        leftSide :: ProverifFormula
        leftSide =
            PVAnd
              (PVEvent PHonest [a1])
              (PVInjEvent PRequest [a2, a1, "s" <> gid, t, sid])

        rightSide :: ProverifFormula
        rightSide =
            PVInjEvent PWitness [a1, a2, "s" <> gid, t]

        body :: ProverifFormula
        body = PVImpl leftSide rightSide
    in ProverifQuery { arguments = args, query = body }
-- "
-- query B:bitstring, WeakAuthBsAtomicKAB:bitstring, s:bitstring,
--       sid:bitstring, t:bitstring, ag:time, i:time, j:time;
--  ((event(eHonest( B ))@ag) && 
--     (inj-event(eRequest( s, B, WeakAuthBsAtomicKAB, t, sid ))@i)) ==>
--  (inj-event(eWitness( B, s, WeakAuthBsAtomicKAB, t ))@j).
-- 
--  query a:bitstring,b:bitstring,c:bitstring,d:bitstring; event(eHonest( b )) && event(eHonest( c )) && event(eHonest( d )) && event(eSecret(a,b,c,d)) && (attacker(a)).
-- "
