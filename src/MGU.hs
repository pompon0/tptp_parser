module MGU(run,eval,State) where

import Skolem(Term(..),VarName)
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.State.Class(get,modify)
import Control.Monad.Trans.Class(lift)
import qualified Data.Map as Map


type State = Map.Map VarName Term
type M = StateM.StateT State (ExceptM.Except ())

throw :: M a
throw = lift $ ExceptM.throwE ()

-- substitution is a function V-FV -> T[FV], represented by acyclic V-FV->T[V] function
-- TODO: early exit in case of identical terms (compared by hash)
-- Note that if you assign hashes to free variables and maintain the hashes for (V-FV)
-- (i.e. updating them on assign), mgu will process only the branches which actually end with a nontrivial assignment.
assign :: VarName -> Term -> M ()
assign xn t = do
  let { has t = case t of { TVar vn -> xn==vn; TFun _ args -> any has args } }
  case t of { TVar n | n==xn -> return (); _ -> do
    s <- get
    case Map.lookup xn s of {
      Just _ -> throw;
      Nothing -> if has t then throw else modify (Map.insert xn t)
    }
  }

run :: (Term,Term) -> State -> Maybe State
run lr s = case ExceptM.runExcept (StateM.runStateT (mgu lr) s) of
  Left _ -> Nothing
  Right (_,s) -> Just s

eval :: State -> Term -> Term
eval s t@(TVar vn) = case Map.lookup vn s of { Nothing -> t; Just t' -> eval s t' }
eval s (TFun f args) = TFun f (map (eval s) args)

mgu :: (Term,Term) -> M ()
mgu (x,y) = case (x,y) of
  (TFun f1 a1, TFun f2 a2) | f1 == f2 -> mapM_ mgu (zip a1 a2)
  -- TODO: you can implement path compression here
  (TFun _ _, TVar _) -> mgu (y,x)
  (TVar xn, _) -> do
    s <- get
    case Map.lookup xn s of
      Nothing -> assign xn y
      Just t -> mgu (t,y)
  _ -> throw


