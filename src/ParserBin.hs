{-# LANGUAGE OverloadedLabels #-}
module ParserBin(main,toDNF) where

import qualified Data.ProtoLens.TextFormat as TextFormat
import Lens.Micro((.~),(^.),(&))
import Lens.Labels.Unwrapped ()
import Data.Either


import qualified Form
import qualified Trace
import qualified Parser
import qualified NNF
import qualified Skolem
import qualified DNF

assert :: Either String a -> IO a
assert (Left errMsg) = fail errMsg
assert (Right v) = return v

toDNF :: String -> IO (Either String DNF.Form)
toDNF input = do
  resOrErr <- Trace.evalIO (Parser.parse input)
  case resOrErr of
    Left errStack -> return $ Left $ unlines errStack
    Right res -> do
      return $ fmap (DNF.dnf . Skolem.skol . NNF.nnf) (Form.fromProto res) 

main = do
  getContents >>= toDNF >>= assert >>= print

