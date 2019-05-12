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

tests = testGroup "TableauxTest" (
  makeTests "brand" Tableaux.proveBrand <>
  makeTests "axiomatic" Tableaux.proveAxiomatic)

makeTests proverName prover = map (\(name,tptpRaw) -> testCase (proverName ++ "." ++ name) $ runTest prover tptpRaw) P.problems

runTest prover tptpString = do
  tptpFile <- Trace.evalIO (Parser.parse tptpString) >>= assert
  form <- assert $ toDNF tptpFile
  --putStrLn ("\n=== BEGIN FORM ===\n" ++ show form ++ "\n=== END FORM ===\n")
  proof <- prover form 15 >>= assertMaybe
  --putStrLn "problem"
  --print form
  --putStrLn "proof source"
  --print (Proof.sourceClauses proof)
  --putStrLn "proof terminal"
  --print (Proof.terminalClauses proof)
  Proof.check form proof
