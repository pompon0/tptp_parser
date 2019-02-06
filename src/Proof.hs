module Proof where

import Lib
import Skolem(Term(..),Subst(..),PredName,FunName)
import qualified Proto.Proof as P
import qualified Data.Map as Map

data Pred = Pred PredName [Term]
data Atom = PosAtom Pred | NegAtom Pred

instance Show Pred where
  show (Pred n x) = show n ++ "(" ++ sepList x ++ ")"
 
instance Show Atom where
  show (PosAtom p) = "+" ++ show p
  show (NegAtom p) = "-" ++ show p

instance Subst Pred where
  subst f (Pred n x) = subst f x >>= return . Pred n

instance Subst Atom where
  subst f (PosAtom p) = subst f p >>= return . PosAtom
  subst f (NegAtom p) = subst f p >>= return . NegAtom

type AllocState = Map.Map Int Term
data Clause = Clause [Atom] AllocState deriving(Show)
type Proof = [Clause]

_Term'toProto :: Term -> P.Term
_Term'toProto = error ""

_Atom'toProto :: Atom -> P.Atom
_Atom'toProto = error ""

_Subst'toProto :: AllocState -> P.Subst
_Subst'toProto = error ""

_Clause'toProto :: Clause -> P.Clause
_Clause'toProto = error ""

_Proof'toProto :: Proof -> P.Proof
_Proof'toProto = error ""

