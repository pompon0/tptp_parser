{-# LANGUAGE OverloadedLabels #-}
module ParserBin(main,toDNF) where

import qualified Data.ProtoLens.TextFormat as TextFormat
import Lens.Micro((.~),(^.),(&))
import Lens.Labels.Unwrapped ()
import Data.Either
import qualified Data.ProtoLens.TextFormat as TextFormat
import qualified Data.Text.Lazy as Text

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



--TODO: move the quantifiers down, convert to CNF (treating quantified formulas as atoms),
--  which will give you a decomposition into subproblems
toDNF :: T.File -> Either String DNF.Form
toDNF tptpFile = fmap (DNF.simplify . DNF.dnf . Skolem.skol . NNF.nnf) (Form.fromProto tptpFile) 

main = do
  textProto <- getContents
  tptpFile <- assert $ TextFormat.readMessage (Text.pack textProto)
  form <- assert $ toDNF tptpFile
  -- TODO: add debugs to LazyParam to see where it gets stuck
  -- TODO: test against simple problems from Harrison's book
  killable $ Tableaux.proveLoop form 20
