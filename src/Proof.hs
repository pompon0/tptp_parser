{-# LANGUAGE OverloadedLabels #-}
module Proof where

import Lib
import Skolem(Term(..),Subst(..))
import qualified DNF
import qualified Proto.Proof as P
import qualified Data.Map as Map
import Data.ProtoLens(defMessage)
import Lens.Micro((.~),(^.),(&))
import Lens.Labels.Unwrapped ()
import qualified Data.Set.Monad as SetM
import Control.Monad(foldM)

import qualified Control.Monad.Trans.Except as ExceptM

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

type AllocState = Map.Map VarName Term
data Clause = Clause [Atom] AllocState deriving(Show)
type Proof = [Clause]

-----------------------------------------------------

eqPredName :: PredName
eqPredName = 0

toDNF'Pred (Pred n args) = case n of
  0 -> case args of
    [l,r] -> return (DNF.PEq l r)
    _ -> Nothing
  _ -> return (DNF.PCustom (n-1) args)

toDNF'Clause (Clause atoms as) = do
  let {
    append cla (PosAtom p) = do { p' <- toDNF'Pred p; return cla { DNF.neg = SetM.insert p' $ DNF.pos cla } };
    append cla (NegAtom p) = do { p' <- toDNF'Pred p; return cla { DNF.pos = SetM.insert p' $ DNF.neg cla } };
  }
  subst (\vn -> Map.lookup vn as) atoms >>= foldM append (DNF.Cla SetM.empty SetM.empty)

toDNF :: Proof -> Maybe DNF.Form
toDNF proof = do
  clauses <- mapM toDNF'Clause proof
  return $ DNF.Form (SetM.fromList clauses)

-----------------------------------------------------

_Term'toProto :: Term -> P.Term
_Term'toProto (TVar vn) = defMessage
  & #type' .~ P.Term'VAR
  & #name .~ fromIntegral vn
_Term'toProto (TFun fn args) = defMessage
  & #type' .~ P.Term'EXP
  & #name .~ fromIntegral fn
  & #args .~ map _Term'toProto args

_Atom'toProto :: Atom -> P.Atom
_Atom'toProto (PosAtom (Pred pn args)) = defMessage
  & #pos .~ True
  & #name .~ fromIntegral pn
  & #args .~ map _Term'toProto args
_Atom'toProto (NegAtom (Pred pn args)) = defMessage
  & #pos .~ False
  & #name .~ fromIntegral pn
  & #args .~ map _Term'toProto args

_Subst'toProto :: (VarName,Term) -> P.Subst
_Subst'toProto (vn,t) = defMessage
  & #varName .~ fromIntegral vn
  & #term .~ _Term'toProto t

_Clause'toProto :: Clause -> P.Clause
_Clause'toProto (Clause atoms as) = defMessage
  & #atom .~ map _Atom'toProto atoms
  & #subst .~ map _Subst'toProto (Map.toList as)

toProto :: Proof -> P.Proof
toProto clauses = defMessage
  & #clause .~ map _Clause'toProto clauses

_Term'fromProto :: P.Term -> Term
_Term'fromProto term = case term^. #type' of
  P.Term'VAR -> TVar (fromIntegral $ term^. #name)
  P.Term'EXP -> TFun (fromIntegral $ term^. #name) (map _Term'fromProto $ term^. #args)
  _ -> error "unknown term type"

_Atom'fromProto ::  P.Atom -> Atom
_Atom'fromProto atom =
  let pred = Pred (fromIntegral $ atom^. #name) (map _Term'fromProto $ atom^. #args)
  in case atom^. #pos of { True -> PosAtom pred; False -> NegAtom pred }

_Subst'fromProto :: P.Subst -> (VarName,Term)
_Subst'fromProto sub = (fromIntegral (sub^. #varName), _Term'fromProto (sub^. #term))

_Clause'fromProto :: P.Clause -> Clause
_Clause'fromProto cla = Clause
  (map _Atom'fromProto (cla^. #atom))
  (Map.fromList $ map _Subst'fromProto (cla^. #subst))

fromProto :: P.Proof -> Proof
fromProto proof = map _Clause'fromProto (proof^. #clause)

