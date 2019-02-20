module Valid(valid) where

import Lib
import DNF
import Skolem
import Prelude hiding(pred)
import Control.Monad(join)
import qualified Data.Set as Set
import Control.Lens((&),(%~))

neg :: Atom -> Atom
neg a = a & atom'sign %~ not 

setVal :: Atom -> OrForm -> OrForm
setVal a f = f
  & orForm'andClauses %~ filter (\c -> not (elem (neg a) $ c^.andClause'atoms))
  & orForm'andClauses.traverse.andClause'atoms %~ filter (/=a)

validRec :: [Pred] -> OrForm -> Bool
validRec preds f@(OrForm clauses) = case clauses of
    [] -> False
    _ | elem (AndClause []) clauses -> True
    _ -> case preds of
      [] -> error ""
      (h:t) -> (validRec t (setVal (Atom True h) f)) && (validRec t (setVal (Atom False h) f))

valid :: OrForm -> Bool
valid f = validRec (unique $ f^..orForm'andClauses.traverse.andClause'atoms.traverse.atom'pred) f

