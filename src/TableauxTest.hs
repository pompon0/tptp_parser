module TableauxTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion,testCaseSteps,testCase,assertFailure,assertBool,(@=?))

import Lib
import qualified Tableaux
import qualified Parser
import qualified Trace
import qualified Proof
import ParserBin(toDNF)
import qualified TptpSampleData as P

tests = testGroup "TableauxTest" (map (\(name,tptpRaw) -> testCase name $ runTest tptpRaw) P.problems)

runTest tptpString = do
  tptpFile <- Trace.evalIO (Parser.parse tptpString) >>= assert
  form <- assert $ toDNF tptpFile
  --putStrLn ("\n=== BEGIN FORM ===\n" ++ show form ++ "\n=== END FORM ===\n")
  proof <- Tableaux.proveLoop form 20 >>= assertMaybe >>= return . Proof.terminalClauses
  print proof


