module Main (main) where

import qualified Choreo.AnalysisTest as AnalysisTest
import qualified Choreo.ComposeTest as ComposeTest
import qualified Choreo.FrameTest as FrameTest
import qualified Choreo.ParsingTest as ParsingTest
import qualified Choreo.TranslationTest as ChoreoTest
import qualified ChoreoToNoname.TranslationSteps.BranchingSendTranslationTest as BranchTest
import qualified ChoreoToNoname.TranslationSteps.SequentializeTranslationTest as SeqTest
import Test.Tasty (TestTree, defaultMain, testGroup)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "All tests"
    [ FrameTest.tests,
      ComposeTest.tests,
      AnalysisTest.tests,
      ChoreoTest.tests,
      BranchTest.tests,
      SeqTest.tests,
      ParsingTest.tests
    ]
