module ParserTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion,testCaseSteps,testCase,assertFailure,assertBool,(@=?))

import Data.Either

import ParserBin(toDNF)
import ConvBin(pullEntries)
import qualified Parser
import qualified Trace
import qualified Form
import qualified NNF
import qualified Skolem
import qualified DNF
import Lib

tests = testGroup "ParserTest" [testCaseSteps "ParserTest" test]

stats :: [Int] -> IO ()
stats x = do
  putStrLn ""
  putStrLn $ "count = " ++ show (length x)
  putStrLn $ "min = " ++ show (minimum x)
  putStrLn $ "max = " ++ show (maximum x)
  putStrLn $ "avg = " ++ show (fromIntegral (sum x) / fromIntegral (length x))

test step = do
  let testEntry (path,content) = parseTest content
  pullEntries >>= mapM testEntry >>= stats

parseTest :: String -> IO Int
parseTest content = do
  DNF.Form x <- toDNF content >>= assert
  return (length x)

