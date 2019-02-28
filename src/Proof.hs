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

data Clause = Clause { _clause'andClause :: AndClause, _clause'val :: Valuation } deriving(Show)
makeLenses ''Clause
type Proof = [Clause]

-----------------------------------------------------

val'lookup :: Valuation -> VarName -> Term
val'lookup val vn = case Map.lookup vn val of { Just t -> t; Nothing -> TVar vn }

andClause'subst :: Traversal AndClause AndClause VarName Term
andClause'subst = andClause'atoms.traverse.atom'pred.pred'spred.spred'args.traverse.term'subst

toDNF'Clause :: Clause -> AndClause
toDNF'Clause (Clause c v) = c & andClause'subst %~ val'lookup v

sourceClauses :: Proof -> OrForm
sourceClauses proof = OrForm $ map (\(Proof.Clause c _) -> c) proof

terminalClauses :: Proof -> OrForm
terminalClauses proof = OrForm $ proof & traverse %~ toDNF'Clause

-----------------------------------------------------

check :: Monad m => DNF.OrForm -> Proof -> m ()
check problem proof = if not (DNF.isSubForm (sourceClauses proof) (DNF.appendEqAxioms problem))
  then fail "proof doesn't imply the formula"
  else case counterExample (terminalClauses proof) of
    Nothing -> return ()
    Just e -> fail (show e)

-----------------------------------------------------

_Term'toProto :: Term -> P.Term
_Term'toProto (TVar vn) = defMessage
  & #type' .~ P.Term'VAR
  & #name .~ fromIntegral vn
_Term'toProto (TFun fn args) = defMessage
  & #type' .~ P.Term'EXP
  & #name .~ fromIntegral fn
  & #args .~ map _Term'toProto args

_Atom'toProto :: Atom -> P.Atom
_Atom'toProto atom = defMessage
  & #sign .~ atom^.atom'sign
  & #name .~ (fromIntegral $ atom^.atom'pred.pred'spred.spred'name)
  & #args .~ map _Term'toProto (atom^.atom'pred.pred'spred.spred'args)

_Subst'toProto :: (VarName,Term) -> P.Subst
_Subst'toProto (vn,t) = defMessage
  & #varName .~ fromIntegral vn
  & #term .~ _Term'toProto t

_Clause'toProto :: Clause -> P.Clause
_Clause'toProto (Clause (AndClause atoms) val) = defMessage
  & #atom .~ map _Atom'toProto atoms
  & #subst .~ map _Subst'toProto (Map.toList val)

toProto :: Proof -> P.Proof
toProto clauses = defMessage
  & #clause .~ map _Clause'toProto clauses

_Term'fromProto :: P.Term -> Term
_Term'fromProto term = case term^. #type' of
  P.Term'VAR -> TVar (fromIntegral $ term^. #name)
  P.Term'EXP -> TFun (fromIntegral $ term^. #name) (map _Term'fromProto $ term^. #args)
  _ -> error "unknown term type"

_Atom'fromProto ::  P.Atom -> Atom
_Atom'fromProto atom =
  let pred = SPred (fromIntegral $ atom^. #name) (map _Term'fromProto $ atom^. #args) ^. from pred'spred
  in DNF.Atom (atom^. #sign) pred

_Subst'fromProto :: P.Subst -> (VarName,Term)
_Subst'fromProto sub = (fromIntegral (sub^. #varName), _Term'fromProto (sub^. #term))

_Clause'fromProto :: P.Clause -> Clause
_Clause'fromProto cla = Clause
  (AndClause $ map _Atom'fromProto (cla^. #atom))
  (Map.fromList $ map _Subst'fromProto (cla^. #subst))

fromProto :: P.Proof -> Proof
fromProto proof = map _Clause'fromProto (proof^. #clause)

