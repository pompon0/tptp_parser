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
import qualified Valid

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Set.Monad as SetM
{-
toValid'Clause :: DNF.Cla -> [DNF.Pred]
toValid'Clause cla = map (Valid.Atom True) (SetM.toList $ DNF.pos cla) ++ map (Valid.Atom False) (SetM.toList $ DNF.neg cla)

toValid'Form :: DNF.Form -> Valid.Form
toValid'Form form =
  let form' = map toValid'Clause (DNF.cla form) in
    let index = Map.fromList (zip [0..] (Set.toList $ Set.fromList $ join form')) in
      case mapM (mapM Map.lookup) form' of
        Nothing -> error "BUG"
        Just form'' -> form''
-}

check :: PT.File -> PP.Proof -> IO Bool
check problemProto proofProto = do
  problem <- assert $ ParserBin.toDNF problemProto
  let proof :: Proof.Proof = Proof.fromProto proofProto
  let sourceClauses = Proof.sourceClauses proof 
  let terminalClauses = Proof.terminalClauses proof
  if not (DNF.isSubForm sourceClauses problem) then return False else do {
    return True  
  }


main = do
  [problemPath,proofPath] <- getArgs
  problemProto :: PT.File <- readProtoFile problemPath
  proofProto :: PP.Proof <- readProtoFile proofPath
  ok <- check problemProto proofProto
  print ok
  

