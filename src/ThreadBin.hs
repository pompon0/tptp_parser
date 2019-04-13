{-# LANGUAGE ScopedTypeVariables #-}
module ThreadBin(main) where

import System.Environment(getArgs)
import Control.Exception(evaluate)
import Lib

import qualified DNF
import ConvBin(pullInteresting,pullSimple)
import ParserBin(toDNF)
import qualified Tableaux
import qualified LazyParam
import Proof(check)

proveAndCheck :: (String, DNF.OrForm) -> (String, IO String)
proveAndCheck (name, problem) = (,) name $ do
  mProof <- LazyParam.proveLoop problem 100
  case mProof of
    Nothing -> return "proof not found"
    Just proof -> do
      check problem proof
      return "ok"

main = do
  --[tarPath] <- getArgs
  --forms <- readProtoTar tarPath >>= mapM (\(k,p) -> assert (toDNF p) >>= return . (,) k)
  forms <- pullSimple >>= mapM (\(k,p) -> assert (toDNF p) >>= return . (,) k)
  let timeout_us = 5*1000000
  killable $ runInParallelWithTimeout timeout_us $ map proveAndCheck forms
  return ()
