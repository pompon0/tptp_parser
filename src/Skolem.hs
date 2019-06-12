{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Skolem(Form(..), skol) where

import Lib
import Pred
import qualified Control.Monad.State.Lazy as StateM
import Control.Lens (makeLenses, (^.), (%~), (.~), over, view, use, (.=), (%=))
import qualified Data.Map as Map
import qualified NNF as F
import Data.List(intercalate)
import qualified Data.Set.Monad as Set
import Control.Monad(join)
import Control.Lens(makeLenses,Traversal,Traversal',Fold,Lens,Lens',Iso',dimap)

data Form = And [Form]
  | Or [Form]
  | PosAtom Pred
  | NegAtom Pred
  deriving(Eq)

instance Show Form where
  show (And x) = "and( " ++ sepList x ++ ")"
  show (Or x) = "or(" ++ sepList x ++ ")"
  show (PosAtom p) = show p
  show (NegAtom n) = "-" ++ show n

--------------------------------------

data State = State {
  _funNames :: Map.Map FunName FunName,
  _varStack :: [Term],
  _nextVar :: VarName,
  _nextFunName :: FunName
}
makeLenses ''State
type M = StateM.State State
empty = State Map.empty [] 0 0


skol :: F.Form -> Form
skol f = let (res,_) = StateM.runState (skolF f) empty in res

-- all the functions get renamed during skolemization
lookupFunName :: FunName -> M FunName
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

psimplify1
  Not False ->  True
  Not True -> False
  Not (Not p) = p
  And p False = False
  And False p = False
  And p True = p
  And True p = p
  Or p False = p
  Or False p = p
  Or p True = True
  Or True p = True
  Imp False p = True
  Imp p True = True
  Imp True p = p
  Imp p False = Not p
  Iff p True = p
  Iff True p = p
  Iff p False = Not p
  Iff False p = Not p
  ? = ?
psimplify fm = {apply psimplify1 bottom up on the subexpressions}

simplify1
  Forall x p = x\in p ? Forall x p : p
  Exists x p = x\in p ? Exists x p : p

simplify fm = {apply simplify1 bottom up on the subexpressions}

nnf (And p q) = And (nnf p) (nnf q)
nnf (Or p q) = Or (nnf p) (nnf q)
nnf (Imp p q) = Or (nnf (not p)) (nnf q)
nnf (Iff p q) = Or (And (nnf p) (nnf q)) (And (nnf (Not p)) (nnf (Not q)))
nnf (Not (Not p)) = nnf p
nnf (Not (And p q)) = Or (nnf (Not p)) (nnf (Not q))
nnf (Not (Or p q)) = And (nnf (Not p)) (nnf (Not q))
nnf (Not (Imp p q)) = And (nnf p) (nnf (Not q))
nnf (Not (Iff p q)) = Or (And (nnf p) (Not (nnf q))) (And (Not (nnf p)) (nnf q))
... forall/exists
nnf ? = ?

nnf2 = nnf . psimplify

skolem (Exists y p) = 
  vars = {free vars in p} - {y}
  return $ skolem (replace y in p with f_y(vars))
skolem (Forall x p) = return $ Forall x (skolem p)
skolem (And p q) = and (skolem p) (skolem q)
skolem (Or p q) = or (skolem p) (skolem q)
skolem ? = ?

generalize fm = {prepend Forall quantifiers for all free vars of fm}

askolemize fm = skolem (nnf2 (simplify fm))
tab fm = tableau [askolemize $ Not $ generalize fm]

purednf (And p q) = {sum all pairs from (purednf p) and (purednf q)}
purednf (Or p q) = {sum (purednf p) and (purednf q)}
purednf ? = [[?]]
purecnf fm = {negation of purednf (nnf (Not fm))}

list_conj l = {Connect all literals in list l with And }
simpdnf fm = {nontrivial, not subsumed elements of purednf (nnf fm)}
simpcnf fm = {nontrivial, not subsumed elements of purecnf (fm)} // nnf can be skipped, because it is applied inside purecnf

specialize fm = {drop leading Forall quantifiers}
prenex fm = {run pullquants bottom-up on subexpressions of fm}


pnf fm = prenex (nnf (simplify fm))
pure_resolution fm = resloop {used=[], unused=simpcnf(specialize(pnf fm))}
resolution fm = map (pure_resolution ** list_conj) (simpdnf $ askolemize $ Not $ generalize fm)

exponential blowup:
  removing <=>
  conversion to DNF

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
    let isVar t = case unwrap t of { TVar _->True; _-> False }
    n <- use nextFunName
    nextFunName %= (+1)
    st <- use varStack
    push (wrap $ TFun n (filter isVar st)) (skolF x)
  F.Exists x -> do
    nv <- use nextVar
    nextVar %= (+1)
    push (wrap $ TVar nv) (skolF x)
  F.Or x -> mapM skolF x >>= return .Or
  F.And x -> mapM skolF x >>= return . And
  F.PosAtom p -> skolP p >>= return . PosAtom
  F.NegAtom p -> skolP p >>= return . NegAtom

skolP :: Pred -> M Pred
skolP p = case unwrap p of
  PEq l r -> do
    sl <- skolT l
    sr <- skolT r
    return (wrap $ PEq sl sr)
  PCustom name args -> mapM skolT args >>= return . wrap . PCustom name
skolT t = case unwrap t of
  TVar vn -> do
    mt <- use (varStack.ix vn)
    case mt of
      Nothing -> fail "oob"
      Just t -> return t
  TFun name args -> do
    n <- lookupFunName name
    a <- mapM skolT args
    return (wrap $ TFun n a)

