{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Form where

import Prelude hiding(fail)
import Control.Monad.Trans.Class(lift)
import qualified Control.Monad.Identity as Identity
import qualified Control.Monad.Trans.Except as Except
import qualified Control.Monad.State.Lazy as StateM
import qualified Data.Map as Map
import Lens.Micro((.~),(^.),(&))
import Lens.Labels.Unwrapped ()
import qualified Data.Text as Text
import qualified Data.List as List

import Lib
import qualified Proto.Tptp as T

type FunName = Int
type PredName = Int
type VarRef = Int

data Form = Forall Form
  | Exists Form
  | And [Form]
  | Or [Form]
  | Xor Form Form
  | Neg Form
  | Atom Pred
  deriving(Eq)

data Pred = PEq Term Term | PCustom PredName [Term] deriving(Eq)
data Term = TVar VarRef | TFun FunName [Term] deriving(Eq)

instance Show Form where
  show (Forall f) = "A " ++ show f
  show (Exists f) = "E " ++ show f
  show (And x) = "and(" ++ sepList x ++ ")"
  show (Or x) = "or(" ++ sepList x ++ ")"
  show (Xor l r) = "xor(" ++ sepList [l,r] ++ ")"
  show (Neg f) = "-" ++ show f
  show (Atom p) = show p
instance Show Pred where
  show (PEq l r) = "eq(" ++ sepList [l,r] ++ ")"
  show (PCustom n x) = show n ++ "(" ++ sepList x ++ ")"
instance Show Term where
  show (TVar n) = "$" ++ show n
  show (TFun n x) = show n ++ "(" ++ sepList x ++ ")"

fromProto :: T.File -> Either String Form 
fromProto f = let
  (res,_) = StateM.runState (Except.runExceptT (_File'fromProto f)) (State Map.empty Map.empty [])
  in res

---------------------------------------

data State = State {
  predNames :: Map.Map (Text.Text,Int) PredName,
  funNames :: Map.Map (Text.Text,Int) FunName,
  varStack :: [Text.Text]
}

type M = Except.ExceptT String (StateM.State State)

fail :: String -> M a
fail msg = Except.throwE msg

push :: [Text.Text] -> M a -> M a
push names ma = do
  stack <- StateM.get >>= return . varStack
  StateM.modify (\s -> s {varStack = (names ++ stack)})
  a <- ma
  StateM.modify (\s -> s {varStack = stack }) 
  return a

lookupPredName :: (Text.Text,Int) -> M PredName
lookupPredName name = do
  s <- StateM.get
  let (i,pn) = getUnique name (predNames s)
  StateM.put $ s { predNames = pn }
  return i

lookupFunName :: (Text.Text,Int) -> M FunName
lookupFunName name = do
  s <- StateM.get
  let (i,fn) = getUnique name (funNames s)
  StateM.put $ s { funNames = fn }
  return i

lookupTVar :: Text.Text -> M Int
lookupTVar name = do
  s <- StateM.get
  case (List.elemIndex name (varStack s)) of
    Just i -> return i
    Nothing -> fail ("variable " ++ show name ++ " not bound")

_File'fromProto :: T.File -> M Form
_File'fromProto f = do
  let m = splitBy (\i -> i^. #role) (f^. #input) 
  let unknown = Map.filterWithKey (\r _ -> not (elem r [T.Input'AXIOM,T.Input'CONJECTURE])) m
  if unknown /= Map.empty then fail ("unexpected roles: " ++ show unknown) else do
    formulas <- (mapM.mapM) (\(i::T.Input)-> _Form'fromProto (i^. #formula)) m
    let axioms = Map.findWithDefault [] T.Input'AXIOM formulas
    let conjs = Map.findWithDefault [] T.Input'CONJECTURE formulas
    return $ Or [Neg (And axioms),And conjs]

_Form'fromProto :: T.Formula -> M Form
_Form'fromProto f =
  case f^. #maybe'formula of 
    Nothing -> fail "field missing"
    Just (T.Formula'Pred' pred) -> _Pred'fromProto (pred) >>= return . Atom
    Just (T.Formula'Quant' quant) -> do {
      c <- (case (quant^. #type') of
        T.Formula'Quant'FORALL -> return Forall
        T.Formula'Quant'EXISTS -> return Exists
        _ -> fail "Formula'Quant'UNKNOWN");
      let { vars = quant^. #var };
      f <- push vars (_Form'fromProto (quant^. #sub));
      return $ foldl (\x _-> c x) f vars
    }
    Just (T.Formula'Op op) -> do { 
      let { args2pair args = case args of { [l,r] -> return (l,r); _ -> fail "args != [l,r]" }};
      args <- mapM _Form'fromProto (op^. #args);
      case (op^. #type') of
        T.Formula'Operator'NEG -> do {
          arg <- (case args of
            [h] -> return h
            _ -> fail "args != [h]");
          return (Neg arg)
        }
        T.Formula'Operator'OR -> return (Or args)
        T.Formula'Operator'AND -> return (And args)
        T.Formula'Operator'IFF -> do {
          (l,r) <- args2pair args;
          return (Neg (Xor l r));
        }
        T.Formula'Operator'IMPL -> do {
          (l,r) <- args2pair args;
          return (Or [(Neg l),r]);
        }
        T.Formula'Operator'XOR -> do {
          (l,r) <- args2pair args;
          return (Xor l r);
        }
        T.Formula'Operator'NOR -> return (Neg (Or args))
        T.Formula'Operator'NAND -> return (Neg (And args))
        _ -> fail "Formula'Operator'UNKNOWN'";
    }

_Pred'fromProto :: T.Formula'Pred -> M Pred
_Pred'fromProto pred = do
  args <- mapM _Term'fromProto (pred^. #args)
  case (pred^. #type') of
    T.Formula'Pred'CUSTOM -> do {
      name <- lookupPredName (pred^. #name, length args);
      return (PCustom name args);
    }
    T.Formula'Pred'EQ -> case args of
      [l,r] -> return (PEq l r)
      _ -> fail "args != [l,r]"
    _ -> fail "pred.type unknown"

_Term'fromProto :: T.Term -> M Term
_Term'fromProto term = case (term^. #type') of
  T.Term'VAR -> lookupTVar (term^. #name) >>= return . TVar
  T.Term'EXP -> do {
    args <- mapM _Term'fromProto (term^. #args);
    name <- lookupFunName (term^. #name, length args);
    return (TFun name args);
  }
  _ -> fail "term.type unknown"
