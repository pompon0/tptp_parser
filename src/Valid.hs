{-# LANGUAGE TemplateHaskell #-}
module Valid(counterExample) where

import Lib
import DNF
import Pred
import Prelude hiding(pred)
import Control.Monad(join)
import qualified Data.Set as Set
import Control.Lens(makeLenses,(&),(%~),(^.),(^..))
import Control.Monad.Except as ExceptM

neg :: Atom -> Atom
neg a = a & atom'sign %~ not 

data State = State { _state'orForm :: OrForm, _state'val :: Set.Set Atom }
makeLenses ''State

setVal :: Atom -> State -> State
setVal a s = s
  & state'val %~ Set.insert a
  & state'orForm.orForm'andClauses %~ filter (\c -> not (elem (neg a) $ c^.andClause'atoms))
  & state'orForm.orForm'andClauses.traverse.andClause'atoms %~ filter (/=a)

validRec :: [Pred] -> State -> ExceptM.Except (Set.Set Atom) ()
validRec preds s = case s^.state'orForm.orForm'andClauses of
    [] -> ExceptM.throwError (s^.state'val)
    _ | elem (AndClause []) (s^.state'orForm.orForm'andClauses) -> return ()
    _ -> case preds of
      [] -> error ""
      (h:t) -> do
        validRec t (setVal (Atom True h) s)
        validRec t (setVal (Atom False h) s)

counterExample :: OrForm -> Maybe (Set.Set Atom)
counterExample f = let
  preds = unique $ f^..orForm'andClauses.traverse.andClause'atoms.traverse.atom'pred
  in case ExceptM.runExcept (validRec preds (State f Set.empty)) of
    Left e -> Just e
    Right () -> Nothing

