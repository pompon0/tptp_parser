{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module Proof where

import Lib
import DNF
import Pred
import qualified Proto.Proof as P
import qualified Data.Map as Map
import Data.ProtoLens(defMessage)
import Lens.Micro((.~),(&),(%~))
import Lens.Labels.Unwrapped ()
import qualified Data.Set.Monad as SetM
import Control.Monad(foldM)
import Control.Lens(makeLenses,Traversal',Traversal,Lens',from)
import Data.Monoid(Endo(..))
import Data.Functor.Const(Const(..))
import Valid(counterExample)

import qualified Control.Monad.Trans.Except as ExceptM

type Proof = OrForm

-----------------------------------------------------

val'lookup :: Valuation -> VarName -> Term
val'lookup val vn = case Map.lookup vn val of { Just t -> t; Nothing -> wrap $ TVar vn }

andClause'subst :: Traversal AndClause AndClause VarName Term
andClause'subst = andClause'atoms.traverse.atom'pred.pred'spred.spred'args.traverse.term'subst

andClause'term :: Traversal' AndClause Term
andClause'term = andClause'atoms.traverse.atom'args.traverse

-----------------------------------------------------

--check :: Monad m => DNF.OrForm -> Proof -> m ()
check :: DNF.OrForm -> Proof -> IO ()
check problem proof =  do
  let proofEssence = OrForm $ filter (not. DNF.isEqAxiom) (proof^.orForm'andClauses)
  printE "problem:"
  printE problem
  printE "problem with axioms:"
  printE (DNF.appendEqAxioms problem)
  printE "proof:"
  printE proof
  printE "proofEssence:"
  printE proofEssence
  if not (DNF.isSubForm proofEssence problem)
  then fail "proof doesn't imply the formula"
  else case counterExample proof of
    Nothing -> return ()
    Just e -> do
      printE ("counter example: " ++ show e)
      fail (show e)

-----------------------------------------------------

_Term'toProto :: Term -> P.Term
_Term'toProto t = case unwrap t of
  TVar vn -> defMessage
    & #type' .~ P.Term'VAR
    & #name .~ fromIntegral vn
  TFun fn args -> defMessage
    & #type' .~ P.Term'EXP
    & #name .~ fromIntegral fn
    & #args .~ map _Term'toProto args

_Atom'toProto :: Atom -> P.Atom
_Atom'toProto atom = defMessage
  & #sign .~ atom^.atom'sign
  & #name .~ (fromIntegral $ atom^.atom'name)
  & #args .~ map _Term'toProto (atom^.atom'args)

_Subst'toProto :: (VarName,Term) -> P.Subst
_Subst'toProto (vn,t) = defMessage
  & #varName .~ fromIntegral vn
  & #term .~ _Term'toProto t

_Clause'toProto :: AndClause -> P.Clause
_Clause'toProto (AndClause atoms) = defMessage
  & #atom .~ map _Atom'toProto atoms

toProto :: Proof -> P.Proof
toProto proof = defMessage
  & #clause .~ map _Clause'toProto (proof^.orForm'andClauses)

_Term'fromProto :: P.Term -> Term
_Term'fromProto term = case term^. #type' of
  P.Term'VAR -> wrap $ TVar (fromIntegral $ term^. #name)
  P.Term'EXP -> wrap $ TFun (fromIntegral $ term^. #name) (map _Term'fromProto $ term^. #args)
  _ -> error "unknown term type"

_Atom'fromProto ::  P.Atom -> Atom
_Atom'fromProto atom =
  let pred = SPred (fromIntegral $ atom^. #name) (map _Term'fromProto $ atom^. #args) ^. from pred'spred
  in DNF.Atom (atom^. #sign) pred

_Subst'fromProto :: P.Subst -> (VarName,Term)
_Subst'fromProto sub = (fromIntegral (sub^. #varName), _Term'fromProto (sub^. #term))

_Clause'fromProto :: P.Clause -> AndClause
_Clause'fromProto cla = AndClause $ map _Atom'fromProto (cla^. #atom)

fromProto :: P.Proof -> Proof
fromProto proof = OrForm $ map _Clause'fromProto (proof^. #clause)

