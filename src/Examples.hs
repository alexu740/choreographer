{-# LANGUAGE OverloadedStrings #-}

module Examples where

import Types.Choreography (Atomic (..), CDefault (..), Choreography (..), Term (..))
import Types.Simple (FUNCTIONS (..), Mode (..))

protocolBAC :: Choreography
protocolBAC =
  let lockC = Lock "C" . Choice Star "x" ["t1", "t2"] . Nonce "N" . Unlock
      msgCR =
        Composed
          PAIR
          [ Composed PAIR [Atomic "x", Atomic "N"],
            Composed SCRYPT [Composed (UnDef "sk") [Atomic "x"], Atomic "N", Atomic "fixedR"]
          ]
      msgRC_ok = Interaction "R" "C" [(Atomic "ok", Nil)] Epsilon
      msgRC_formatErr = Interaction "R" "C" [(Atomic "formatErr", Nil)] Epsilon
      lockR msgok msgerr =
        Lock "R"
          . Read "State" "noncestate" (Atomic "N")
          $ If
            (Atomic "State")
            (Atomic "fresh")
            (Write "noncestate" (Atomic "N") (Atomic "spent") . Unlock $ msgok)
            (Unlock msgerr)
   in lockC $
        Interaction
          "C"
          "R"
          [(msgCR, lockR msgRC_ok msgRC_formatErr)]
          (Otherwise msgRC_formatErr)
