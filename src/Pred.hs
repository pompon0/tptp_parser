{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Pred where

import Lib
import Control.Lens(makeLenses,Traversal,Traversal',Fold,Lens,Lens',Iso',dimap)
import qualified Data.Map as Map

data Term = TVar VarName | TFun FunName [Term] deriving(Eq,Ord)
data Pred = PEq Term Term | PCustom PredName [Term]

sort a b = if a<b then [a,b] else [b,a]
conv (PEq a b) = (0,0,sort a b)
conv (PCustom n a) = (1,n,a)

instance Eq Pred where
  (==) a b = conv a == conv b
instance Ord Pred where
  (<=) a b = conv a <= conv b

term'subst :: Traversal Term Term VarName Term
term'subst g (TVar vn) = g vn
term'subst g (TFun fn args) = pure (TFun fn) <*> (traverse.term'subst) g args

term'subterm :: Fold Term Term
term'subterm g t@(TFun fn args) = (traverse.term'subterm) g args *> g t *> pure t
term'subterm g t = g t *> pure t

data SPred = SPred { _spred'name :: PredName, _spred'args :: [Term] }
makeLenses ''SPred

eqPredName = -1

makeSPred :: Pred -> SPred
makeSPred (PEq l r) = SPred eqPredName [l,r]
makeSPred (PCustom pn args) = SPred pn args

makePred :: SPred -> Pred
makePred (SPred pn args) = case args of
  [l,r] | pn == eqPredName -> PEq l r
  _ -> PCustom pn args 

pred'spred :: Iso' Pred SPred
pred'spred = dimap makeSPred (fmap makePred)

instance Show Pred where
  show (PEq l r) = "eq(" ++ sepList [l,r] ++ ")"
  show (PCustom n x) = show n ++ "(" ++ sepList x ++ ")"

instance Show Term where
  show (TVar n) = show n
  show (TFun n x) = show n ++ "(" ++ sepList x ++ ")"

----------------------------------------------------

-- Valuation is a function V-FV -> T[FV], represented by acyclic V-FV -> T[V] function
type Valuation = Map.Map VarName Term

emptyValuation = Map.empty

-- function T[V] -> T[FV], represented by the valuation
eval :: Valuation -> Term -> Term
eval s t@(TVar vn) = case Map.lookup vn s of { Nothing -> t; Just t' -> eval s t' }
eval s (TFun f args) = TFun f (map (eval s) args)

