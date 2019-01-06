module ParserTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion,testCaseSteps,testCase,assertFailure,assertBool,(@=?))

import Data.Either

import ConvBin(pullEntries)
import qualified Parser
import qualified Trace
import qualified Form
import qualified NNF
import qualified Skolem

tests = testGroup "ParserTest" [testCaseSteps "ParserTest" test]

test step = do
  let testEntry (path,content) = do { step path; parseTest content }
  pullEntries >>= mapM_ testEntry

assert :: Either String a -> IO a
assert (Left errMsg) = assertFailure errMsg
assert (Right v) = return v

parseTest :: String -> Assertion
parseTest content = do 
  resOrErr <- Trace.evalIO (Parser.parse content)
  case resOrErr of
    Left errStack -> assertFailure (show errStack)
    Right res -> do
      form <- assert $ Form.fromProto res
      let skol = Skolem.skol (NNF.nnf form)
      return ()
