{-# LANGUAGE OverloadedLabels #-}
module ParserBin(main) where

import qualified Data.ProtoLens.TextFormat as TextFormat
import Lens.Micro((.~),(^.),(&))
import Lens.Labels.Unwrapped ()
import Data.Either

import qualified Form
import qualified Trace
import qualified Parser
import qualified NNF
import qualified Skolem

assert :: Either String a -> IO a
assert (Left errMsg) = fail errMsg
assert (Right v) = return v

main = do
  input <- getContents
  putStrLn input
  resOrErr <- Trace.evalIO (Parser.parse input)
  case resOrErr of
    Left errStack -> do
      putStrLn ":: ERROR ::"
      mapM_ putStrLn errStack
    Right res -> do
      f <- assert $ Form.fromProto res
      --putStrLn $ show f
      let nnf = NNF.nnf f
      putStrLn $ "\n" ++ show nnf
      let skol = Skolem.skol nnf
      putStrLn $ "\n" ++ show skol

