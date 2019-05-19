{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Form where

import Prelude hiding(fail)
import Control.Monad(join,when)
import Control.Monad.Trans.Class(lift)
import qualified Control.Monad.Identity as Identity
import qualified Control.Monad.Trans.Except as Except
import qualified Control.Monad.State.Lazy as StateM
import qualified Data.Map as Map
import Control.Lens((.~),(&),(^.))
import Lens.Labels.Unwrapped ()
import qualified Data.Text as Text
import qualified Data.List as List
import Data.Ix(Ix)
import qualified Data.Set as Set
import Data.Set((\\))

import Lib
import qualified Proto.Tptp as T

newtype VarRef = VarRef Int deriving(Eq,Num,Ord,Ix)
instance Show VarRef where { show (VarRef x) = show x }

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
  (res,_) = StateM.runState (Except.runExceptT (fromProto'File f)) (State Map.empty Map.empty [])
  in res

---------------------------------------

preds :: Form -> [Pred]
preds f = case f of
  Forall x -> preds x
  Exists x -> preds x
  Neg x -> preds x
  And x -> join (map preds x)
  Or x -> join (map preds x)
  Xor x y -> preds x ++ preds y
  Atom x -> [x]

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

lookupTVar :: Text.Text -> M VarRef
lookupTVar name = do
  s <- StateM.get
  case (List.elemIndex name (varStack s)) of
    Just i -> return (fromIntegral i)
    Nothing -> fail ("variable " ++ show name ++ " not bound")

fromProto'File :: T.File -> M Form
fromProto'File f = mapM fromProto'Input (f^. #input) >>= return.Or

fromProto'Input :: T.Input -> M Form
fromProto'Input i = do
  let { freeVars = unique $ freeVars'Formula (i^. #formula) };
  case i^. #language of {
    T.Input'CNF -> return ();
    T.Input'FOF -> when (freeVars/=mempty) $ fail "unexpected free vars in FOF";
    language@_ -> fail ("unexpected language: " ++ show language);
  };
  form <- push freeVars (fromProto'Form (i^. #formula)) >>= (\f -> return $ foldl (\x _-> Forall x) f freeVars);
  case i^. #role of {
    T.Input'AXIOM -> return $ Neg form;
    T.Input'PLAIN -> return $ Neg form;
    T.Input'NEGATED_CONJECTURE -> return $ Neg form;
    T.Input'CONJECTURE -> return form; 
    role@_ -> fail ("unexpected role: " ++ show role);
  };

fromProto'Form :: T.Formula -> M Form
fromProto'Form f =
  case f^. #maybe'formula of 
    Nothing -> fail "field missing"
    Just (T.Formula'Pred' pred) -> _Pred'fromProto (pred) >>= return . Atom
    Just (T.Formula'Quant' quant) -> do {
      c <- (case (quant^. #type') of
        T.Formula'Quant'FORALL -> return Forall
        T.Formula'Quant'EXISTS -> return Exists
        _ -> fail "Formula'Quant'UNKNOWN");
      let { vars = quant^. #var };
      f <- push vars (fromProto'Form (quant^. #sub));
      return $ foldl (\x _-> c x) f vars
    }
    Just (T.Formula'Op op) -> do { 
      let { args2pair args = case args of { [l,r] -> return (l,r); _ -> fail "args != [l,r]" }};
      args <- mapM fromProto'Form (op^. #args);
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
        T.Formula'Operator'TRUE -> return (And [])
        T.Formula'Operator'FALSE -> return (Or [])
        op@_ -> fail ("unexpected operator:" ++ show op)
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


freeVars'Term :: T.Term -> [Text.Text]
freeVars'Term t = case t^. #type' of {
  T.Term'VAR -> [t^. #name];
  T.Term'EXP -> t^. #args >>= freeVars'Term;
}

freeVars'Formula :: T.Formula -> [Text.Text]
freeVars'Formula f = case f^. #maybe'formula of {
  Nothing -> [];
  Just (T.Formula'Pred' pred) -> pred^. #args >>= freeVars'Term;
  Just (T.Formula'Quant' quant) -> Set.toAscList $ Set.fromList (freeVars'Formula $ quant^. #sub) \\ Set.fromList (quant^. #var);
  Just (T.Formula'Op op) -> op^. #args >>= freeVars'Formula;
}

