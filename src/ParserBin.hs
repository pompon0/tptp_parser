{-# LANGUAGE OverloadedLabels #-}
module ParserBin(main) where

import qualified Data.ProtoLens.TextFormat as TextFormat
import Lens.Micro((.~),(^.),(&))
import Lens.Labels.Unwrapped ()
import Data.Either

import qualified Form
import qualified Trace
import qualified Parser


main = do
  input <- getContents
  print input
  resOrErr <- Trace.evalIO (Parser.parse input)
  case resOrErr of
    Left errStack -> do
      putStrLn ":: ERROR ::"
      mapM_ putStrLn errStack
    Right res -> do
      let formulas = map (\i -> i^. #formula) (res^. #input)
      mapM (\f -> putStrLn $ show $ Form.fromProto $ f) formulas
      putStrLn (TextFormat.showMessage res) 
