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
import qualified Data.Set.Monad as Set
import Lib

tests = testGroup "ParserTest" [testCaseSteps "ParserTest" test]

isPEq (DNF.PEq _ _) = True
isPEq _ = False

frac :: Int -> Int -> Double
frac num den = fromIntegral num / fromIntegral den

simpl :: DNF.Form -> [[DNF.Pred]]
simpl (DNF.Form x) = [Set.toList p ++ Set.toList n | DNF.Cla p n <- Set.toList x]

stats :: [DNF.Form] -> IO ()
stats f = do
  let c = map simpl f
  let x = map length c
  putStrLn ""
  let proTotal = length x
  let claTotal = sum x
  putStrLn $ "total(pro) = " ++ show proTotal
  putStrLn $ "total(cla) = " ++ show claTotal
  putStrLn $ "min(cla/pro) = " ++ show (minimum x)
  putStrLn $ "max(cla/pro) = " ++ show (maximum x)
  putStrLn $ "avg(cla/pro) = " ++ show (frac claTotal proTotal)
  let lc = map (map length) c
  let ec = map (map (length . filter isPEq)) c
  let litTotal = sum (map sum lc)
  let peqTotal = sum (map sum ec)
  putStrLn $ "total(lit) = " ++ show litTotal
  putStrLn $ "min(lit/cla) = " ++ show (minimum (map minimum lc))
  putStrLn $ "max(lit/cla) = " ++ show (maximum (map maximum lc))
  putStrLn $ "avg(lit/cla) = " ++ show (frac litTotal claTotal)
  putStrLn $ "avg(lit/pro) = " ++ show (frac litTotal proTotal)
  putStrLn $ "total(peq) = " ++ show peqTotal
  putStrLn $ "avg(peq/cla) = " ++ show (frac peqTotal claTotal)
  putStrLn $ "avg(peq/pro) = " ++ show (frac peqTotal proTotal)

test step = do
  let testEntry (path,content) = toDNF content >>= assert
  pullEntries >>= mapM testEntry >>= stats

