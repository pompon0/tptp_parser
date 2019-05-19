{-# LANGUAGE ScopedTypeVariables #-}
module ThreadBin(main) where

import Options
import System.Environment(getArgs)
import Control.Exception(evaluate)
import Control.Lens((^.),to,non,at)
import Control.Monad(filterM)
import qualified Data.Map as Map
import Data.List(intercalate,sort)
import Lib

import qualified DNF
import ConvBin(isInteresting,isSimple,isAverage,pullAll,pullAllCNF)
import ParserBin(toDNF)
import qualified Tableaux
import qualified LazyParam
import Proof(check)

enumOption :: (Bounded a, Enum a, Show a) => String -> a -> DefineOptions a
enumOption name def = defineOption enumOptionType
  (\o -> o { optionLongFlags = [name], optionDefault = def }) where
    enumOptionType = optionType setString minBound parseEnum show
    values = Map.fromList [(show x, x) | x <- enumFrom minBound]
    setString = "{" ++ intercalate ", " (map show (Map.keys values)) ++ "}"
    parseEnum s = case Map.lookup s values of
      Nothing -> Left (show s ++ " is not in " ++ setString ++ ".")
      Just x -> Right x

data Prover = LazyParam | BrandTableau | AxiomaticTableau deriving(Bounded,Enum,Show)
data TestSet = FOF | EproverCNF deriving(Bounded,Enum,Show)
data TestFilter = All | Simple | Average | Interesting deriving(Bounded,Enum,Show)

data Args = Args {
  prover :: Prover,
  testSet :: TestSet,
  testFilter :: TestFilter,
  timeoutSec :: Int,
  testName :: String
} deriving(Show)

instance Options Args where
  defineOptions = pure Args
    <*> enumOption "prover" LazyParam
    <*> enumOption "test_set" FOF
    <*> enumOption "test_filter" All
    <*> simpleOption "timeout_sec" 5 ""
    <*> simpleOption "test_name" "" ""

proveAndCheck :: Prover -> (String, DNF.OrForm) -> (String, IO String)
proveAndCheck prover (name, problem) = (,) name $ do
  mProof <- (case prover of {
    LazyParam -> LazyParam.proveLoop;
    BrandTableau -> Tableaux.proveBrand;
    AxiomaticTableau -> Tableaux.proveAxiomatic;
  }) problem 200
  case mProof of
    Nothing -> return "proof not found"
    Just proof -> do
      check problem proof
      return "ok"

main = runCommand $ \(args :: Args) _ -> do
  --[tarPath] <- getArgs
  --forms <- readProtoTar tarPath >>= mapM (\(k,p) -> assert (toDNF p) >>= return . (,) k)
  forms <- do
    x <- case testSet args of {
      FOF -> pullAll;
      EproverCNF -> pullAllCNF;
    }
    let f = case testFilter args of {
      All -> (\_ -> return True);
      Simple -> isSimple;
      Average -> isAverage;
      Interesting -> isInteresting;
    }
    filterM f (sort x)
  let forms' = if testName args/="" then filter (\(k,_) -> k==testName args) forms else forms
  forms'' <- mapM (\(k,p) -> assert (toDNF p) >>= return . (,) k) forms'
  let timeout_us = fromIntegral $ (timeoutSec args)*1000000
  killable $ runInParallelWithTimeout timeout_us $ map (proveAndCheck $ prover args) forms''
  return ()
