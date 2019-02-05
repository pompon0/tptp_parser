{-# LANGUAGE ScopedTypeVariables #-}
module ThreadBin(main) where

import Control.DeepSeq(force)
import Control.Exception(evaluate)
import Lib

import qualified DNF
import ConvBin(pullEntries)
import ParserBin(toDNF)
import LazyParam(proveLoop) 

import Control.DeepSeq(NFData)
import GHC.Generics(Generic)

main = do
  let entryToDNF (path,content) = toDNF content >>= assert
  forms <- pullEntries >>= evaluate.force >>= mapM entryToDNF
  let timeout_us = 2*1000000
  res <- killable $ runInParallelWithTimeout timeout_us $ map (\f -> proveLoop f 10) forms
  return ()
