{-# LANGUAGE OverloadedLabels #-}
module ParserBin(main,toDNF) where

import qualified Data.ProtoLens.TextFormat as TextFormat
import Lens.Micro((.~),(^.),(&))
import Lens.Labels.Unwrapped ()
import Data.Either

import Lib
import qualified Form
import qualified Trace
import qualified Parser
import qualified NNF
import qualified Skolem
import qualified DNF

toDNF :: String -> IO (Either String DNF.Form)
toDNF input = do
  resOrErr <- Trace.evalIO (Parser.parse input)
  case resOrErr of
    Left errStack -> return $ Left $ unlines errStack
    Right res -> do
      --TODO: move the quantifiers down, convert to CNF (treating quantified formulas as atoms),
      --  which will give you a decomposition into subproblems
      return $ fmap (DNF.simplify . DNF.dnf . Skolem.skol . NNF.nnf) (Form.fromProto res) 

main = do
  getContents >>= toDNF >>= assert >>= print

