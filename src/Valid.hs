module Valid(valid,Atom(..),Clause,Form) where

import Lib
import Prelude hiding(pred)
import Control.Monad(join)
import qualified Data.Set as Set

data Atom = Atom { pos :: Bool, pred :: PredName } deriving(Eq)
type Clause = [Atom]
type Form = [Clause]

neg :: Atom -> Atom
neg a = a { pos = not (pos a) }

setVal :: Atom -> Form -> Form
setVal val form = map (filter (/= val)) $ filter (elem (neg val)) form

validRec :: [PredName] -> Form -> Bool
validRec predNames form = case form of
    [] -> False
    _ | elem [] form -> True
    _ -> case predNames of
      [] -> error ""
      (h:t) -> (validRec t (setVal (Atom True h) form)) && (validRec t (setVal (Atom False h) form))

valid :: Form -> Bool
valid form = validRec (Set.toList $ Set.fromList $ map pred (join form)) form

