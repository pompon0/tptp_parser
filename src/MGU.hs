module MGU(runMGU) where

import Pred
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.State.Class(get,modify)
import Control.Monad.Trans.Class(lift)
import qualified Data.Map as Map
import Debug.Trace
import Control.Lens(at,(.=))

import Lib

type M = StateM.StateT Valuation (ExceptM.Except ())

throw :: M a
throw = lift $ ExceptM.throwE ()

-- TODO: early exit in case of identical terms (compared by hash)
-- Note that if you assign hashes to free variables and maintain the hashes for (V-FV)
-- (i.e. updating them on assign), mgu will process only the branches which actually end with a nontrivial assignment.
assign :: VarName -> Term -> M ()
assign xn t = do
  s <- get
  let {
    -- TODO: we can even do free vars caching, instead of traversal
    has t = case unwrap t of
      TVar vn -> case Map.lookup vn s of { Nothing -> vn==xn; Just t -> has t };
      TFun _ args -> any has args;
  }
  case unwrap t of {
    -- break on trivial assignment
    TVar vn | vn==xn -> return ();
    -- traverse TVar assignments
    TVar vn -> case Map.lookup vn s of {
      Nothing -> at xn .= Just t;
      Just t' -> assign xn t';
    };
    -- perform TFun assignment (but check for loop)
    _ -> if has t then throw else at xn .= Just t;
  }

runMGU :: (Term,Term) -> Valuation -> Maybe Valuation
runMGU lr s = case ExceptM.runExcept (StateM.runStateT (mgu lr) s) of
  Left _ -> Nothing
  Right (_,s) -> Just s

mgu :: (Term,Term) -> M ()
mgu (x,y) = if x==y then return () else case (unwrap x, unwrap y) of
    (TFun f1 a1, TFun f2 a2) | f1 == f2 -> mapM_ mgu (zip a1 a2)
    -- TODO: you can implement path compression here
    (TFun _ _, TVar _) -> mgu (y,x)
    (TVar xn, _) -> do
      s <- get
      case Map.lookup xn s of
        Nothing -> assign xn y
        Just t -> mgu (t,y)
    _ -> throw


