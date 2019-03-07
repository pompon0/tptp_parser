{-# LANGUAGE ScopedTypeVariables #-}
module CheckerBin(main,check) where

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

check :: PT.File -> PP.Proof -> IO Bool
check problemProto proofProto = do
  problem <- assert $ ParserBin.toDNF problemProto
  let proof :: Proof.Proof = Proof.fromProto proofProto
  putStrLn ("problem = " ++ show problem)
  putStrLn ("proof = " ++ show proof)
  if not (DNF.isSubForm (DNF.OrForm proof) problem) then return False else do {
    case counterExample (DNF.OrForm proof) of
      Nothing -> return True
      Just e -> do
        putStrLn("counter example: " ++ show e)
        return False
  }


main = do
  [problemPath,proofPath] <- getArgs
  problemProto :: PT.File <- readProtoFile problemPath
  proofProto :: PP.Proof <- readProtoFile proofPath
  ok <- check problemProto proofProto
  print ok
  

