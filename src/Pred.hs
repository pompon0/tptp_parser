{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Pred where

import Control.Monad.IO.Class(MonadIO,liftIO)
import Lib
import Control.Lens(makeLenses,Traversal,Traversal',Fold,Lens,Lens',Iso',dimap)
import qualified Data.Map as Map
import Data.HashCons(HC,hc,getVal,HashCons,Hashable)
import Data.HashCons.Memo()
import GHC.Generics(Generic)

data Term' = TVar VarName | TFun FunName [Term]
  deriving stock (Eq, Generic, Ord)
  deriving anyclass (Hashable, HashCons)
data Pred' = PEq Term Term | PCustom PredName [Term]
  deriving stock (Eq, Generic, Ord)
  deriving anyclass (Hashable, HashCons)
{-
type Term = HC Term'
type Pred = HC Pred'

wrap :: HashCons a => a -> HC a
wrap = hc
unwrap :: HashCons a => HC a -> a
unwrap = getVal
-}

wrap = id
unwrap = id
type Term = Term'
type Pred = Pred'

sort a b = if a<b then [a,b] else [b,a]
conv (PEq a b) = (0,0,sort a b)
conv (PCustom n a) = (1,n,a)

--instance Eq Pred where
--  (==) a b = conv a == conv b
--instance Ord Pred where
--  (<=) a b = conv a <= conv b

--type TraversalIO s t a b = forall f. MonadIO f => (a -> f b) -> (s -> f t)

term'subst :: Traversal Term Term VarName Term
term'subst g t = case unwrap t of
  TVar vn -> g vn
  TFun fn args -> pure wrap <*> (pure (TFun fn) <*> (traverse.term'subst) g args)

term'subterm :: Fold Term Term
term'subterm g t = case unwrap t of
  (TFun fn args) -> (traverse.term'subterm) g args *> g t *> pure t
  _ -> g t *> pure t

data SPred = SPred { _spred'name :: PredName, _spred'args :: [Term] }
makeLenses ''SPred

eqPredName :: PredName
eqPredName = -1

extraConstName :: FunName
extraConstName = -1

makeSPred :: Pred -> SPred
makeSPred p = case unwrap p of
  (PEq l r) -> SPred eqPredName [l,r]
  (PCustom pn args) -> SPred pn args

makePred :: SPred -> Pred
makePred (SPred pn args) = case args of
  [l,r] | pn == eqPredName -> wrap $ PEq l r
  _ -> wrap $ PCustom pn args 

pred'spred :: Iso' Pred SPred
pred'spred = dimap makeSPred (fmap makePred)

instance Show Pred' where
  show p = case p of
    (PEq l r) -> "eq(" ++ sepList [l,r] ++ ")"
    (PCustom n x) -> show n ++ "(" ++ sepList x ++ ")"

instance Show Term' where
  show t = case t of
    (TVar n) -> show n
    (TFun n x) -> show n ++ "(" ++ sepList x ++ ")"

----------------------------------------------------

-- Valuation is a function V-FV -> T[FV], represented by acyclic V-FV -> T[V] function
type Valuation = Map.Map VarName Term

emptyValuation = Map.empty

-- function T[V] -> T[FV], represented by the valuation
eval :: Valuation -> Term -> Term
eval s t = case unwrap t of
  (TVar vn) -> case Map.lookup vn s of { Nothing -> t; Just t' -> eval s t' }
  (TFun f args) -> wrap $ TFun f (map (eval s) args)

-- TODO: rename to ground
terminate :: Term -> Term
terminate t = case unwrap t of
  (TVar _) -> wrap $ TFun extraConstName []
  (TFun f args) -> wrap $ TFun f (map terminate args)


