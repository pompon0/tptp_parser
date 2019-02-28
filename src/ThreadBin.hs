{-# LANGUAGE ScopedTypeVariables #-}
module ThreadBin(main) where

import System.Environment(getArgs)
import Control.DeepSeq(force)
import Control.Exception(evaluate)
import Lib

import qualified DNF
import ConvBin(pullInteresting)
import ParserBin(toDNF)
import Tableaux(proveLoop) 
import Proof(check)

import Control.DeepSeq(NFData)
import GHC.Generics(Generic)

proveAndCheck :: (String, DNF.OrForm) -> (String, IO String)
proveAndCheck (name, problem) = (,) name $ do
  mProof <- proveLoop problem 100
  case mProof of
    Nothing -> return "proof not found"
    Just proof -> do
      check problem proof
      return "ok"

main = do
  --[tarPath] <- getArgs
  --forms <- readProtoTar tarPath >>= mapM (\(k,p) -> assert (toDNF p) >>= return . (,) k)
  forms <- pullInteresting >>= mapM (\(k,p) -> assert (toDNF p) >>= return . (,) k)
  let timeout_us = 2*1000000
  killable $ runInParallelWithTimeout timeout_us $ map proveAndCheck forms
  return ()
