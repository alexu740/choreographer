module Choreo.ParsingTest (tests) where

import Types.Choreography (Choreography)
import Types.ChoreographyProtocolShell (protocolChoreo)
import Choreo.ParsingHelper (prettyPrint)
import qualified Syntax.Lexer as Lexer
import qualified Syntax.Parser as Parser (parser)
import qualified Syntax.Util as SyntaxUtil
import Test.QuickCheck (Property, counterexample, (===))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

tests :: TestTree
tests =
  testGroup
    "Parsing tests"
    [ testProperty "Parse / prettyPrint" prop_parsePrettyInverse
    ] -- QuickCheck property that checks the parsePrettyInverse condition

prop_parsePrettyInverse :: Choreography -> Property
prop_parsePrettyInverse choreo =
  let printed =
        "Protocol: { x : sk(x) } \n"
          ++ prettyPrint choreo

      parsedChoreo =
        ( do
            parsed <- Lexer.runAlex printed Parser.parser
            return $ protocolChoreo parsed
        )
   in counterexample
        ( "Printed:\n"
            ++ printed
            ++ "\nParsed:\n"
            ++ either (const " ") prettyPrint parsedChoreo
        )
        $ parsedChoreo === Right choreo
