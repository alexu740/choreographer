{-# LANGUAGE OverloadedStrings #-}

module Syntax.Util where

import Types.Simple( Constructors, Cell, Identifier, Mode, FUNCTIONS(..))
import Types.Choreography (Agent, Term (..), Choreography)
import Types.LocalBehavior (Domain)
import Types.Rewrite (RewriteRules, RewriteTerm(Atom, Comp) )
import Types.ChoreographyProtocolShell
    ( RoleKnowledge(..),
      RoleInfo(roleChoice, roleKnowledge),
      InitCells,
      Knowledge,
      Roles,
      Sigma(..),
      ProtocolDescription(..) )

import qualified Types.Rewrite as RR
import qualified Data.Either as Either
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Control.Applicative as List
import Data.Text (toLower)

toRR :: Term -> RR.RewriteTerm
toRR (Atomic v) = RR.Atom v
toRR (Composed f subterms) = RR.Comp f (map toRR subterms)

isUnboundTerm :: Set.Set Agent -> Term -> Either RR.RewriteTerm Term
isUnboundTerm unboundRoles (Atomic v)
  | Set.member v unboundRoles = Left $ RR.RewriteVar (RR.UnDef v)
  | otherwise = Right (Atomic v)
isUnboundTerm unboundRoles t@(Composed f subterms)
  | any Either.isLeft subterms' =
      let subtermsRR = map (either id toRR) subterms' 
      in Left $ RR.Comp f subtermsRR
  | otherwise = Right t
  where
    subterms' = map (isUnboundTerm unboundRoles) subterms

getRoleKnowledge :: Set.Set Agent -> [Term] -> RoleKnowledge
getRoleKnowledge unboundRoles =
  foldr
    ( \term roleK ->
        case isUnboundTerm unboundRoles term of
          Left t ->
            roleK {unbounded = t : unbounded roleK}
          Right t ->
            roleK {bounded = t : bounded roleK}
    )
    RoleKnowledge {bounded = [], unbounded = []}

getUnboundRoles :: Roles -> Set.Set Agent
getUnboundRoles =
  Map.keysSet . Map.filter (Maybe.isJust . roleChoice)

getAgentRoleKnowledge :: Roles -> [(Agent, RoleKnowledge)]
getAgentRoleKnowledge roles =
  let setOfRoleNames = getUnboundRoles roles
  in Map.toList $ Map.map (getRoleKnowledge setOfRoleNames . roleKnowledge) roles

getRoleChoices :: Roles -> Map.Map Agent (Mode, Domain)
getRoleChoices =
  Map.map Maybe.fromJust
    . Map.filter Maybe.isJust
    . Map.map roleChoice

mkProtocolDescription :: Sigma -> Sigma -> RewriteRules -> InitCells -> [(Agent, RoleInfo)] -> Choreography -> ProtocolDescription
mkProtocolDescription sigma0 sigma algebra initcells roles choreo =
  ProtocolDescription
    { protocolSigma0 = sigma0,
      protocolSigma = sigma,
      protocolAlgebra = algebra,
      protocolCells = initcells,
      protocolRoles = Map.fromList roles,
      protocolChoreo = choreo,
      protocolGoals = List.empty
    }

mkEmptySigma :: Sigma
mkEmptySigma =
  Sigma
    { public = Map.empty,
      private = Map.empty,
      relation = Map.empty
    }

combinePublicSigma :: Sigma -> Sigma -> Knowledge
combinePublicSigma (Sigma {public = pu1}) (Sigma {public = pu2}) =
  pu1 `Map.union` pu2

removeDestructors :: RewriteRules -> Constructors -> Constructors
removeDestructors destructors constructors =
  Map.difference constructors destructors

getConstructors :: ProtocolDescription -> Constructors
getConstructors protocolDescription =
  let combinedSigma   = combinePublicSigma (protocolSigma0 protocolDescription) (protocolSigma protocolDescription)           
      keysAsFunctions = Map.mapKeys fromText combinedSigma               
      algebra         = protocolAlgebra protocolDescription         
      constructors    = removeDestructors algebra keysAsFunctions
  in constructors


stdConstructors :: Constructors
stdConstructors = Map.fromList [(SCRYPT, 3), (CRYPT, 3), (SIGN, 2), (PAIR, 2), (SESSION, 2), (SID, 1), (PUBK, 1)]

fromText :: T.Text -> FUNCTIONS
fromText func =
  case func of
    "scrypt" -> SCRYPT
    "crypt" -> CRYPT
    "sign" -> SIGN
    "pair" -> PAIR
    "session" -> SESSION
    "sid" -> SID
    "dscrypt" -> DSCRYPT
    "dcrypt" -> DCRYPT
    "open" -> OPEN
    "proj1" -> PROJ1
    "proj2" -> PROJ2
    "sfst" -> SFST
    "ssnd" -> SSND
    "dsid" -> DSID
    "vscrypt" -> VSCRYPT
    "vcrypt" -> VCRYPT
    "vsign" -> VSIGN
    "vpair" -> VPAIR
    "inv" -> INV
    "pubk" -> PUBK
    "hash" -> HASH
-- sapic
    "priv" -> PRIV
    "pk" -> PK
    "aenc" -> AENC
    "senc" -> SENC
    "revealSign" -> REVEALSIGN
    "sk" -> SK
    _ -> UnDef func

toText :: FUNCTIONS -> T.Text
toText SCRYPT = "scrypt"
toText CRYPT = "crypt"
toText SIGN = "sign"
toText PAIR = "pair"
toText SESSION = "session"
toText SID = "sid"
toText DSCRYPT = "dscrypt"
toText DCRYPT = "dcrypt"
toText OPEN = "open"
toText PROJ1 = "proj1"
toText PROJ2 = "proj2"
toText SFST = "sfst"
toText SSND = "ssnd"
toText DSID = "dsid"
toText VSCRYPT = "vscrypt"
toText VCRYPT = "vcrypt"
toText VSIGN = "vsign"
toText VPAIR = "vpair"
toText INV = "inv"
toText PUBK = "pubk"
toText HASH = "hash"
-- sapic
toText PK = "pk"
toText AENC = "aenc"
toText SENC = "senc"
toText REVEALSIGN = "revealSign"
toText REVEALVERIFY = "revealVerify"
toText GETMESSAGE = "getMessage"
toText PRIV = "priv"
toText SK = "sk"

-- sapic
toText (UnDef func) = func
toText f = toLower $ T.pack (show f)

top :: T.Text
top = "__TRUE__"

dummyIdentifier :: T.Text
dummyIdentifier = "__DUMMY__"