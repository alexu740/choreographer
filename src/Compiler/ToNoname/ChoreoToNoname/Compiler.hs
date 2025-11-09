{-# LANGUAGE TupleSections #-}

module Compiler.ToNoname.ChoreoToNoname.Compiler where

import Debug.Pretty.Simple (pTraceM)
import qualified Types.Choreography as Choreo
import qualified Types.Rewrite as ChoreoT
import Compiler.ToLocalBehavior.Translation (translateWithDescription)
import Compiler.ToNoname.ChoreoToNoname.InitialContext (Transaction, prepareInitialContexts)
import Compiler.ToNoname.ChoreoToNoname.InitialTransactions (initialChoreo)
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.BranchingSendTranslation as BranchSend
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.RedundantOperations as RedundantOper
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.RemoveSeq as RemoveSeq
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SeqToNoname as SeqToNoname
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SequentializeTranslation as Sequentialize
import qualified Compiler.ToNoname.ChoreoToNoname.TranslationSteps.SwapOperations as SwapOper
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map
import qualified Data.Text as T
import Compiler.ToNoname.Noname.FilePrinter (printToFile)
import qualified Compiler.ToNoname.Noname.Syntax as Noname
import qualified Syntax.Lexer as Lexer
import qualified Syntax.Parser as Parser
import Types.ChoreographyProtocolShell (ProtocolDescription (..), Sigma (public))

data CompilerError
  = -- | Error during the parsing process.
    ParsingError String
  | -- | Error during the translation process.
    TranslationError ChoreoT.TranslationError
  | -- | Error during the sequentialization process.
    SequentializationError Sequentialize.SequentializeError
  deriving (Show)

-- | Compiles a given input string into a Noname file.
compile :: String -> String -> Either CompilerError String
compile filename input = do
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
compileToNoname :: ChoreoT.Description -> ChoreoT.State -> Choreo.Choreography -> Either CompilerError [Noname.Process]
compileToNoname description state choreo = do
  localBehavior <- either (Left . TranslationError) Right $ translateWithDescription description [(state, choreo)]
  let branchSend = BranchSend.removeBranchingSend localBehavior
  seqLB <- either (Left . SequentializationError) Right $ Sequentialize.sequentialize branchSend
  let seqLB1 = RedundantOper.removeRedundantOperations seqLB
  let seqLB2 = SwapOper.swapOperations seqLB1
  let seqLB3 = RemoveSeq.removeSeq seqLB2
  let seqLB4 = map SwapOper.swapOperations $ NonEmpty.toList seqLB3
  let frame = ChoreoT.frame state
  let noname = map (SeqToNoname.toNonameSeq frame) seqLB4
  return noname
