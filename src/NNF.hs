module NNF(PredName,FunName,VarRef,Form(..),F.Pred(..),F.Term(..)) where

import qualified Form as F

type PredName = F.PredName
type FunName = F.FunName
type VarRef = F.VarRef

data Form = Forall Form
  | Exists Form
  | And [Form]
  | Or [Form]
  | Xor [Form]
  | PosAtom Pred
  | NegAtom Pred
  deriving(Eq,Show)
type Pred = F.Pred

nnf = _nnf False
_nnf :: Bool -> F.Form -> Form
_nnf n f = case f of
  F.Forall x -> (if n then Exists else Forall) (_nnf n x)
  F.Exists x -> (if n then Forall else Exists) (_nnf n x)
  F.And x -> (if n then Or else And) (map (_nnf n) x)
  F.Or x -> (if n then And else Or) (map (_nnf n) x)
  F.Xor x -> Xor (Or[] : map (_nnf n) x)
  F.Neg x -> _nnf (not n) x
  F.Atom p -> (if n then NegAtom else PosAtom) p
