{-# LANGUAGE OverloadedStrings #-}

module Compiler.ToNoname.ChoreoToNoname.InitialTransactions where

import qualified Types.Choreography as C
import qualified Types.Simple as F
import Types.Rewrite (RewriteRules)
import qualified Types.Rewrite as RR
import Choreography.Enricher (stdRewriteRules)
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Map as Map
import qualified Data.Text as T
import Types.ChoreographyProtocolShell (Knowledge, ProtocolDescription (..), RoleInfo (RoleInfo), Sigma (..))
import Syntax.Util (getRoleChoices, toText)

initialChoreo :: ProtocolDescription -> (F.Constructors, ProtocolDescription)
initialChoreo protocolDesc =
  let roleChoice = getRoleChoices $ protocolRoles protocolDesc

      sigma = protocolSigma protocolDesc
      private' =
        Map.unions
          [ private (protocolSigma protocolDesc),
            Map.unions
              . map roleFunctions
              $ Map.keys roleChoice,
            Map.fromList $ map (Bifunctor.first toText) [(F.SESSION, 2), (F.SFST, 1), (F.SSND, 1), (F.SID, 1), (F.DSID, 1)]
          ]
      sigma' = sigma {private = private'}

      algebra' =
        Map.unions
          [ protocolAlgebra protocolDesc,
            Map.unions
              . map destructorRules
              $ Map.keys roleChoice,
            Map.fromList
              [ (F.SFST, stdRewriteRules Map.! F.SFST),
                (F.SSND, stdRewriteRules Map.! F.SSND),
                (F.DSID, stdRewriteRules Map.! F.DSID)
              ]
          ]
      roles' = Map.insert "init" (RoleInfo [] Nothing) (protocolRoles protocolDesc)

      choreo' = initialChoreoRoleChoices protocolDesc

      constructors = map (F.UnDef . constructorName) $ Map.keys roleChoice
      constructors' = Map.fromList $ [(c, 2) | c <- constructors]
   in ( constructors',
        protocolDesc
          { protocolSigma = sigma',
            protocolAlgebra = algebra',
            protocolRoles = roles',
            protocolChoreo = choreo'
          }
      )

initialChoreoRoleChoices :: ProtocolDescription -> C.Choreography
initialChoreoRoleChoices protocolDesc =
  let initAgent = "init"
      initDummyAgent = "initDummy"
      sessionID = "sessionID"

      allRoles = Map.keys . protocolRoles $ protocolDesc
      choiceRoles = Map.toList . getRoleChoices $ protocolRoles protocolDesc
      combine f = foldr ((.) . f) id

      choice (r, (m, d)) = C.Choice m r d

      sendSID ag1 ag2 cont =
        C.Interaction ag1 ag2 [(C.Composed F.SID [C.Atomic sessionID], cont)] C.Epsilon
      sendInit ag1 ag2 x cont =
        C.Interaction ag1 ag2 [(C.Composed (F.UnDef $ constructorName x) [C.Atomic x, C.Atomic sessionID], cont)] C.Epsilon

      sendToDummySID = sendSID initAgent initDummyAgent
      sendToDummyInit = sendInit initAgent initDummyAgent
      sendFromDummySID = sendSID initDummyAgent
      sendFromDummyInit = sendInit initDummyAgent
   in C.Lock
        initAgent
        . C.Nonce sessionID
        . combine choice choiceRoles
        . C.Unlock
        . sendToDummySID
        . combine sendToDummyInit (map fst choiceRoles)
        . combine sendFromDummySID allRoles
        . combine
          (uncurry sendFromDummyInit)
          ( let m' = map fst choiceRoles
             in [ (x1, x2)
                | x1 <- allRoles,
                  x2 <- m'
                ]
          )
        $ protocolChoreo protocolDesc

destructorRules :: C.Agent -> RewriteRules
destructorRules role =
  Map.fromList
    [ (F.UnDef $ destructorName role, ([constructor], RR.RewriteVar (RR.UnDef "x"))),
      (F.UnDef $ rdestructorName role, ([constructor], RR.RewriteVar (RR.UnDef "r")))
    ]
  where
    constructor =
      RR.Comp
        (F.UnDef $ constructorName role)
        [ RR.RewriteVar (RR.UnDef "x"),
          RR.RewriteVar (RR.UnDef "r")
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
