{-# LANGUAGE ScopedTypeVariables #-}
module CheckerBin(main) where

import Lib
import System.Environment(getArgs)
import qualified Data.ProtoLens.TextFormat as TextFormat
import Data.ProtoLens.Message(Message)
import qualified Data.Text.Lazy as Text
import qualified Proto.Proof as PP
import qualified Proto.Tptp as PT
import qualified Proof
import qualified Form
import qualified ParserBin
import qualified DNF
import Valid(counterExample)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Set.Monad as SetM

main = do
  [problemPath,proofPath] <- getArgs
  problemProto :: PT.File <- readProtoFile problemPath
  proofProto :: PT.File <- readProtoFile proofPath
  (problem,nameIndex) <- assert $ DNF.fromProto problemProto Form.emptyNI
  (proof,_) <- assert $ DNF.fromProto proofProto nameIndex
  putStrLn ("problem = " ++ show problem)
  putStrLn ("proof = " ++ show proof)
  Proof.check problem proof
