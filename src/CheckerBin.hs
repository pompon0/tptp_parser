{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedLabels #-}
module CheckerBin(main) where

import Lib
import System.Environment(getArgs)
import qualified Data.ProtoLens.TextFormat as TextFormat
import Data.ProtoLens.Message(Message)
import qualified Data.Text.Lazy as Text
import qualified Proto.Tptp as T
import qualified Proto.Solutions as SPB
import qualified Proof
import qualified Form
import qualified ParserBin
import qualified DNF
import Valid(counterExample)
import qualified Parser
import qualified Trace
import ParserBin(formToDNF)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Set.Monad as SetM
import Control.Lens

readAndParse :: String -> IO T.File
readAndParse tptp_path = do
  content <- readFile tptp_path
  Trace.evalIO (Parser.parse content) >>= assert

help = do
  putStrLn "conv [fof|cnf] [tptp_file] > [proto_file]"
  putStrLn "cnf [fof_proto_file] > [cnf_proto_file]"
  putStrLn "validate [solution_proto_file] > [stats_proto_file]"


conv [language,tptp_path] = do
  case language of {
    "fof" -> readAndParse tptp_path >>= putStrLn . TextFormat.showMessage;
    "cnf" -> do {
      file <- readAndParse tptp_path;
      (dnf,ni) <- assert $ DNF.fromProto file Form.emptyNI;
      assert (DNF.toProto dnf ni) >>= putStrLn . TextFormat.showMessage;
    };
    _ -> help;
  }

cnf [fof_proto_file] = do
  file <- readProtoFile fof_proto_file
  (fof,ni) <- assert $ Form.runM (Form.fromProto'File file) Form.emptyNI
  assert (DNF.toProto (formToDNF fof) ni) >>= putStrLn . TextFormat.showMessage

validate [solution_proto_file] = do
  solutionProto :: SPB.CNF <- readProtoFile solution_proto_file
  ((problem,proof,stats),_) <- assert $ Form.runM (do
    problem <- DNF.fromProto'File (solutionProto^. #problem)
    proof <- DNF.fromProto'File (solutionProto^. #proof)
    stats <- Form.liftRM $ Proof.classify proof problem
    case counterExample proof of
      Nothing -> return ()
      Just x -> fail ("counter example: " ++ show x)
    return (problem,proof,stats)) Form.emptyNI
  putStrLnE ("problem = " ++ show problem)
  putStrLnE ("proof = " ++ show proof)
  putStrLn (TextFormat.showMessage stats)

main = do
  cmd:args <- getArgs
  case cmd of {
    "conv" -> conv args;
    "cnf" -> cnf args;
    "validate" -> validate args;
    _ -> help;
  }
