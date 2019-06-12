module NNF(nnf,Form(..),Pred(..),Term(..)) where

import qualified Form as F
import Pred
import Lib

data Form = Forall Form
  | Exists Form
  | And [Form]
  | Or [Form]
  | PosAtom Pred
  | NegAtom Pred
  deriving(Eq)

instance Show Form where
  show (Forall f) = "A " ++ show f
  show (Exists f) = "E " ++ show f
  show (And x) = "and(" ++ sepList x ++ ")"
  show (Or x) = "or(" ++ sepList x ++ ")"
  show (PosAtom p) = show p
  show (NegAtom p) = "-" ++ show p

nnf :: F.Form -> Form
nnf = _nnf False
_nnf :: Bool -> F.Form -> Form
_nnf n f = case f of
  F.Forall x -> (if n then Exists else Forall) (_nnf n x)
  F.Exists x -> (if n then Forall else Exists) (_nnf n x)
  F.And x -> (if n then Or else And) (map (_nnf n) x)
  F.Or x -> (if n then And else Or) (map (_nnf n) x)
  -- xor elimination allows to pull out the quantifiers
  -- NOTE: this reduction causes exponential blow up
  --       it can be optimized by caching
  F.Xor x y -> _nnf n (F.Or [F.And [F.Neg x,y], F.And [x,F.Neg y]])
  F.Neg x -> _nnf (not n) x
  F.Atom p -> (if n then NegAtom else PosAtom) p
