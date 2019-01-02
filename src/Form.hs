{-# LANGUAGE OverloadedLabels #-}
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

import qualified Proto.Tptp as T

type FunName = Int
type PredName = Int
type Ref = Int

data Form = Forall Form
  | Exists Form
  | And [Form]
  | Or [Form]
  | Xor [Form]
  | Neg Form
  | Atom Pred
  deriving(Eq,Show)

data Pred = Pred'Eq Term Term
  | Pred'Custom { _Pred'name :: PredName, _Pred'args :: [Term] }
  deriving(Eq,Show)

data Term = Var Ref
  | Fun { _Fun'name :: FunName, _Fun'args :: [Term] }
  deriving(Eq,Show)

fromProto :: T.Formula -> Either String Form 
fromProto f = let
  (res,_) = StateM.runState (Except.runExceptT (_Form'fromProto f)) (State Map.empty Map.empty [])
  in res

---------------------------------------

getUnique :: Ord a => a -> Map.Map a Int -> (Int,Map.Map a Int)
getUnique k m = case Map.lookup k m of
  Just i -> (i,m)
  Nothing -> (Map.size m, Map.insert k (Map.size m) m)

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

lookupVar :: Text.Text -> M Int
lookupVar name = do
  s <- StateM.get
  case (List.elemIndex name (varStack s)) of
    Just i -> return i
    Nothing -> fail ("variable " ++ show name ++ " not bound")

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
        T.Formula'Operator'IFF -> return (Neg (Xor args))
        T.Formula'Operator'IMPL -> do {
          (l,r) <- (case args of
            [l,r] -> return (l,r)
            _ -> fail "args != [l,r]");
          return (Or [(Neg l),r])
        }
        T.Formula'Operator'XOR -> return (Xor args)
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
      return (Pred'Custom name args);
    }
    T.Formula'Pred'EQ -> case args of
      [l,r] -> return (Pred'Eq l r)
      _ -> fail "args != [l,r]"
    _ -> fail "pred.type unknown"

_Term'fromProto :: T.Term -> M Term
_Term'fromProto term = case (term^. #type') of
  T.Term'VAR -> lookupVar (term^. #name) >>= return . Var
  T.Term'EXP -> do {
    args <- mapM _Term'fromProto (term^. #args);
    name <- lookupFunName (term^. #name, length args);
    return (Fun name args);
  }
  _ -> fail "term.type unknown"
