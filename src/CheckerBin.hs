{-# LANGUAGE ScopedTypeVariables #-}
module CheckerBin(main) where

import Lib
import System.Environment(getArgs)
import qualified Data.ProtoLens.TextFormat as TextFormat
import Data.ProtoLens.Message(Message)
import qualified Data.Text.Lazy as Text
import qualified Proto.Tptp as T
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

readAndParse :: String -> IO T.File
readAndParse tptp_path = do
  content <- readFile tptp_path
  Trace.evalIO (Parser.parse content) >>= assert

help = do
  putStrLn "conv [fof|cnf] [tptp_file] > [proto_file]"
  putStrLn "cnf [fof_proto_file] > [cnf_proto_file]"
  putStrLn "validate [cnf_proto_problem] [cnf_proto_proof]"


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

validate [cnf_proto_problem,cnf_proto_proof] = do
  problemProto :: T.File <- readProtoFile cnf_proto_problem
  proofProto :: T.File <- readProtoFile cnf_proto_proof
  (problem,nameIndex) <- assert $ DNF.fromProto problemProto Form.emptyNI
  (proof,_) <- assert $ DNF.fromProto proofProto nameIndex
  putStrLn ("problem = " ++ show problem)
  putStrLn ("proof = " ++ show proof)
  Proof.check problem proof

main = do
  cmd:args <- getArgs
  case cmd of {
    "conv" -> conv args;
    "cnf" -> cnf args;
    "validate" -> validate args;
    _ -> help;
  }
