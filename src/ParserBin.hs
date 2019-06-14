module ParserBin(main,toDNF,formToDNF) where

import qualified Data.ProtoLens.TextFormat as TextFormat
import qualified Data.Text.Lazy as Text
import Data.Either

import Lib
import qualified Proto.Tptp as T
import qualified Form
import qualified Trace
import qualified Parser
import qualified NNF
import qualified Skolem
import qualified DNF
import qualified LazyParam
import qualified Tableaux
import qualified Proof

formToDNF :: Form.Form -> DNF.OrForm
formToDNF = DNF.simplify . DNF.dnf . Skolem.skol . NNF.nnf

--TODO: move the quantifiers down, convert to CNF (treating quantified formulas as atoms),
--  which will give you a decomposition into subproblems
toDNF :: T.File -> Either String DNF.OrForm
toDNF tptpFile = fmap formToDNF (Form.fromProto tptpFile) 

main = do
  textProto <- getContents
  tptpFile <- assert $ TextFormat.readMessage (Text.pack textProto)
  print (Form.fromProto tptpFile)
  problem <- assert $ toDNF tptpFile
  print problem
  mProof <- killable $ LazyParam.proveLoop problem 100
  print mProof
  case mProof of
    Nothing -> error "proof not found"
    Just proof -> do
      Proof.check problem proof
      --putStrLn (TextFormat.showMessage $ Proof.toProto proof)
