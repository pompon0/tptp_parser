{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Skolem where

import Lib
import qualified Control.Monad.State.Lazy as StateM
import Control.Lens (makeLenses, (^.), (%~), (.~), over, view, use, (.=), (%=))
import qualified Data.Map as Map
import qualified NNF as F

type PredName = F.PredName
type FunName = Int
type VarName = Int

data Form = And [Form]
  | Or [Form]
  | Xor [Form]
  | PosAtom Pred
  | NegAtom Pred
  deriving(Eq,Show)
data Pred = PEq Term Term | PCustom PredName [Term] deriving(Eq,Show)
data Term = TVar VarName | TFun FunName [Term] deriving(Eq,Show)

data State = State {
  _funNames :: Map.Map F.FunName FunName,
  _varStack :: [Term],
  _nextVar :: VarName,
  _nextFunName :: FunName
}
makeLenses ''State
type M = StateM.State State

lookupFunName :: F.PredName -> M FunName
lookupFunName name = do
  fn <- use funNames
  case Map.lookup name fn of
    Just i -> return i
    Nothing -> do
      i <- use nextFunName
      nextFunName %= (+1)
      funNames %= Map.insert name i
      return i

{-
Amodel Ey Ax f <=>
Amodel Ax(y) Ey f
  for every choice of counter examples x
  exists y for which x(y) is not a counterexample
-}

push :: Term -> M a -> M a
push t ma = do
  st <- use varStack
  varStack .= t:st
  a <- ma
  varStack .= st
  return a 

skolF :: F.Form -> M Form
skolF f = case f of
  F.Forall x -> do
    let isVar t = case t of { TVar _->True; _-> False }
    n <- use nextFunName
    nextFunName %= (+1)
    st <- use varStack
    push (TFun n (filter isVar st)) (skolF x)
  F.Exists x -> do
    nv <- use nextVar
    nextVar %= (+1)
    push (TVar nv) (skolF x)
  F.Or x -> mapM skolF x >>= return .Or
  F.And x -> mapM skolF x >>= return . And
  F.Xor x -> mapM skolF x >>= return . Xor
  F.PosAtom p -> skolP p >>= return . PosAtom
  F.NegAtom p -> skolP p >>= return . NegAtom
skolP p = case p of
  F.PEq l r -> do
    sl <- skolT l
    sr <- skolT r
    return (PEq sl sr)
  F.PCustom name args -> mapM skolT args >>= return . PCustom name
skolT t = case t of
  F.TVar ref -> do
    mt <- use (varStack.ix ref)
    case mt of
      Nothing -> fail "oob"
      Just t -> return t
  F.TFun name args -> do
    n <- lookupFunName name
    a <- mapM skolT args
    return (TFun n a)

