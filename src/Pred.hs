{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}
module Pred where

import Lib
import Control.Lens(makeLenses,Traversal,Traversal',Fold,Lens,Lens',Iso',dimap)
import qualified Data.Map as Map
import HashSeq

data Term' = TVar VarName | TFun FunName [Term]
data Pred' = PEq Term Term | PCustom PredName [Term]

type Term = WithHash Term'
type Pred = WithHash Pred'

instance HashSeq Term' where
  hashSeq (TVar vn) = [unit 0, unit (fromIntegral vn)]
  hashSeq (TFun fn args) = unit 1 : unit (fromIntegral fn) : map hash args

instance HashSeq Pred' where
  hashSeq (PEq a b) = [unit 0,hash a,hash b]
  hashSeq (PCustom pn args) = unit 1 : unit (fromIntegral pn) : map hash args

term'subst :: Traversal Term Term VarName Term
term'subst g (val -> TVar vn) = g vn
term'subst g (val -> TFun fn args) = pure (withHash . TFun fn) <*> (traverse.term'subst) g args

term'subterm :: Fold Term Term
term'subterm g t@(val -> TFun fn args) = (traverse.term'subterm) g args *> g t *> pure t
term'subterm g t@(val -> TVar _) = g t *> pure t

data SPred = SPred { _spred'name :: PredName, _spred'args :: [Term] }
makeLenses ''SPred

wrap :: HashSeq a => a -> WithHash a
wrap = withHash
unwrap :: HashSeq a => WithHash a -> a
unwrap = val

makeSPred :: Pred -> SPred
makeSPred (val -> PEq l r) = SPred eqPredName [l,r]
makeSPred (val -> PCustom pn args) = SPred pn args

makePred :: SPred -> Pred
makePred (SPred pn args) = case args of
  [l,r] | pn == eqPredName -> withHash $ PEq l r
  _ -> withHash $ PCustom pn args 

pred'spred :: Iso' Pred SPred 
pred'spred = dimap makeSPred (fmap makePred)

instance Show Pred where
  show (val -> PEq l r) = "eq(" ++ sepList [l,r] ++ ")"
  show (val -> PCustom n x) = show n ++ "(" ++ sepList x ++ ")"

instance Show Term where
  show (val -> TVar n) = show n
  show (val -> TFun n x) = show n ++ "(" ++ sepList x ++ ")"

----------------------------------------------------

-- Valuation is a function V-FV -> T[FV], represented by acyclic V-FV -> T[V] function
type Valuation = Map.Map VarName Term

emptyValuation = Map.empty

-- function T[V] -> T[FV], represented by the valuation
eval :: Valuation -> Term -> Term
eval s t@(val -> TVar vn) = case Map.lookup vn s of { Nothing -> t; Just t' -> eval s t' }
eval s (val -> TFun f args) = withHash $ TFun f (map (eval s) args)

ground :: Term -> Term
ground (val -> TVar _) = withHash $ TFun extraConstName []
ground (val -> TFun f args) = withHash $ TFun f (map ground args)


