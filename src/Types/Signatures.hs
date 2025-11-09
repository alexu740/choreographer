module Types.Signatures where

import Types.Choreography (Agent, Choreography)
import Types.LocalBehavior (LocalBehavior)
import Types.Rewrite (Description, State, TranslationError)
import Types.Sapic (SProcess, SapicTranslationError)
import Types.ChoreographyProtocolShell (ProtocolDescription)
import Compiler.ToSapicPlus.SFrame (SFrame)

type LocalBehaviorTranslatorFunction =
  Description -> [(State, Choreography)]
  -> Either TranslationError LocalBehavior

type SapicTranslatorFunction = 
  ProtocolDescription -> Agent -> [(SFrame, Choreography)] -> Either SapicTranslationError SProcess