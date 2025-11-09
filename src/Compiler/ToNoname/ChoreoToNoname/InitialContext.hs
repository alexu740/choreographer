{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToNoname.ChoreoToNoname.InitialContext where

import Types.Choreography (Agent)
import Types.Rewrite (State)
import qualified Types.Rewrite as Description
import qualified Types.Simple as F
import Choreography.Enricher (stdRewriteRules)
import qualified Choreography.State as State
import qualified Data.Map as Map
import qualified Data.Text as T
import Compiler.ToNoname.Noname.Syntax (Process)
import Types.ChoreographyProtocolShell (ProtocolDescription (..))
import Syntax.Util (getAgentRoleKnowledge, getConstructors, stdConstructors)

type Transaction = (Agent, Process)

prepareInitialContexts :: F.Constructors -> ProtocolDescription -> [(Description.Description, State)]
prepareInitialContexts constructors protocolDesc =
  let roles = protocolRoles protocolDesc
      initial (ag, roleK) =
        ( Description.Description
            { Description.agent = ag,
              Description.constructors = Map.unions [stdConstructors, getConstructors protocolDesc, constructors],
              Description.rewriteRules = stdRewriteRules `Map.union` protocolAlgebra protocolDesc
            },
          State.mkState roleK
        )
   in map initial $ getAgentRoleKnowledge roles

constructorName :: Agent -> T.Text
constructorName = T.append (T.pack "init")

destructorName :: Agent -> T.Text
destructorName = T.append (T.pack "dinit")

rdestructorName :: Agent -> T.Text
rdestructorName = T.append (T.pack "rinit")
