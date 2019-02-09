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
import qualified Tableaux
import ParserBin(toDNF)

readProtoFile :: Message a => String -> IO a
readProtoFile path = readFile path >>= assert . TextFormat.readMessage . Text.pack 

main = do
  [problemPath,proofPath] <- getArgs
  problemProto :: PT.File <- readProtoFile problemPath
  proofProto :: PP.Proof <- readProtoFile proofPath
  problem <- assert $ toDNF problemProto
  proof <- assertMaybe $ Tableaux.toDNF (Proof.fromProto proofProto)
  print problem
  print proof
