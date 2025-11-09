{-# LANGUAGE TupleSections #-}

module Compiler.Compiler where

import Types.Simple (Constructors)
import Types.Rewrite (Description(..), TranslationError, State(..), Frame(..))
import Types.LocalBehavior (LocalBehavior)
import Types.Choreography (Choreography)
import Types.ChoreographyProtocolShell (ProtocolDescription (..), Sigma (public, private))

import qualified Syntax.Lexer as Lexer
import qualified Syntax.Parser as Parser

import qualified Compiler.ToLocalBehavior.Translation as LocalBehaviorTranslator
import qualified Compiler.ToSapicPlus.Translation as SapicTranslator
import qualified Compiler.ToSapicPlus.PrettyPrinter as PP

import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.BranchingSendTranslation as BranchSend
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.RedundantOperations as RedundantOper
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.RemoveSeq as RemoveSeq
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqToNoname as SeqToNoname
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SequentializeTranslation as Sequentialize
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SwapOperations as SwapOper
import qualified Compiler.ToNoname.Noname.Syntax as Noname
import Compiler.ToLocalBehavior.Translation (translateWithDescription)
import Compiler.ToNoname.ChoreoToNoname.InitialContext (Transaction, prepareInitialContexts)
import Compiler.ToNoname.ChoreoToNoname.InitialTransactions (initialChoreo)
import Compiler.ToNoname.Noname.FilePrinter (printToFile)

import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map
import qualified Data.Text as T

data CompilerError
  = ParsingError String -- | Error during the parsing process.
  | TranslationError TranslationError  -- | Error during the translation process.
  | SequentializationError Sequentialize.SequentializeError
  deriving (Show)

-- | Parses a given input string into a ProtocolDescription.
parseInputFile :: String -> Either CompilerError ProtocolDescription
parseInputFile input = either (Left . ParsingError) Right $ Lexer.runAlex input Parser.parser

-- | Compiles a given input string into a Noname file.
compile :: String -> String -> String -> Either CompilerError String
compile target filename input = do
  case target of
    -- sapic / tamarin
    "sapic" -> do
      protocolDescription <- parseInputFile input
      let translated = SapicTranslator.translateProtocol protocolDescription
      case translated of
        Right translatedProtocol -> Right (PP.prettySProtocol translatedProtocol)
        Left err -> Left (ParsingError (T.unpack err))
    -- noname
    "noname" -> startCompilationToNoname filename input
  
-- Noname & Localbehavior --
startCompilationToNoname :: String -> String -> Either CompilerError String
startCompilationToNoname filename input = do
  (protocolDesc, transactions) <- compileHelper input
  return (printToFile filename protocolDesc transactions)

-- | Compile helper function.
compileHelper :: String -> Either CompilerError (ProtocolDescription, [Transaction])
compileHelper input = do
  protocolDesc <- parsing input
  -- TODO : improve
  let numbers = map ((,0) . T.pack . (("N" ++) . show)) ([0 .. 9] :: [Int])
  let sigma = protocolSigma protocolDesc
  let sigma' = sigma {public = public sigma `Map.union` Map.fromList numbers}
  let protocolDesc1 = protocolDesc {protocolSigma = sigma'}

  let (constructors, protocolDesc2) = initialChoreo protocolDesc1

  let initialContexts = prepareInitialContexts constructors protocolDesc2
  compiled <-
    mapM
      ( \(description, state) ->
          compileToNoname description state (protocolChoreo protocolDesc2)
      )
      initialContexts
  let transactions = Map.keys (protocolRoles protocolDesc2) `zip` compiled

  let flattenT =
        concatMap
          ( \(r, xs) -> case xs of
              [] -> []
              [x] -> [(r, x)]
              _ -> zipWith (\i x -> (r `T.append` T.pack (show i), x)) [1 :: Int ..] xs
          )
  return (protocolDesc2, flattenT transactions)

-- | Parses a given input string into a ProtocolDescription.
parsing :: String -> Either CompilerError ProtocolDescription
parsing input =
  either
    (Left . ParsingError)
    Right
    $ Lexer.runAlex input Parser.parser

-- | Compiles a choreography for a given agent and frame into a Noname process.
--   This function performs the entire transformation pipeline, returning either
--   a translation error or the resulting Noname process.
compileToNoname ::  Description -> State -> Choreography -> Either CompilerError [Noname.Process]
compileToNoname description state choreo = do
  localBehavior <- either (Left . TranslationError) Right $ translateWithDescription description [(state, choreo)]

  let branchSend = BranchSend.removeBranchingSend localBehavior
  seqLB <- either (Left . SequentializationError) Right $ Sequentialize.sequentialize branchSend
  let seqLB1 = RedundantOper.removeRedundantOperations seqLB
  let seqLB2 = SwapOper.swapOperations seqLB1
  let seqLB3 = RemoveSeq.removeSeq seqLB2
  let seqLB4 = map SwapOper.swapOperations $ NonEmpty.toList seqLB3
  let noname = map (SeqToNoname.toNonameSeq (frame state)) seqLB4
  return noname