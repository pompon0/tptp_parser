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

import Control.DeepSeq(NFData)
import GHC.Generics(Generic)

main = do
  --[tarPath] <- getArgs
  --forms <- readProtoTar tarPath >>= mapM (\(k,p) -> assert (toDNF p) >>= return . (,) k)
  forms <- pullInteresting >>= mapM (\(k,p) -> assert (toDNF p) >>= return . (,) k)
  let timeout_us = 2*1000000
  res <- killable $ runInParallelWithTimeout timeout_us $ map (\(n,f) -> (n,proveLoop f 100)) forms
  return ()
