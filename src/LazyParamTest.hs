module LazyParamTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion,testCaseSteps,testCase,assertFailure,assertBool,(@=?))

import Lib
import qualified LazyParam
import qualified Parser
import qualified Trace
import qualified Proof
import qualified TptpSampleData as P
import ParserBin(toDNF)

tests = testGroup "LazyParamTest" (map (\(name,tptpRaw) -> testCase name $ runTest tptpRaw) P.problems)

runTest tptpString = do
  tptpFile <- Trace.evalIO (Parser.parse tptpString) >>= assert
  form <- assert $ toDNF tptpFile
  --putStrLn ("\n=== BEGIN FORM ===\n" ++ show form ++ "\n=== END FORM ===\n")
  proof <- LazyParam.proveLoop form 15 >>= assertMaybe
  --putStrLn "problem"
  --print form
  --putStrLn "proof source"
  --print (Proof.sourceClauses proof)
  --putStrLn "proof terminal"
  --print (Proof.terminalClauses proof)
  Proof.check form proof


