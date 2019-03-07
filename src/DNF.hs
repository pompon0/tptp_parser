{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module DNF(
  dnf, simplify, isSubForm,
  Atom(..), atom'sign, atom'pred, atom'name, atom'args, opposite,
  OrForm(..), orForm'andClauses,
  AndClause(..), andClause'atoms,
  NotAndForm(..), notAndForm'orClauses,
  OrClause(..), orClause'atoms,
  notOrClause, notAndClause,
  toNotAndForm, toOrForm,
  appendEqAxioms,
) where

import Prelude hiding(pred)
import Pred
import qualified Skolem
import Lib
import qualified MGU
import qualified Data.List.Ordered as Ordered
import Control.Monad(foldM)
import Control.Lens(Traversal',Lens',Fold,filtered,makeLenses,(&),(%~))
import Data.List(intercalate)
import Data.List.Utils (replace)

data Atom = Atom { _atom'sign :: Bool, _atom'pred :: Pred } deriving(Eq,Ord)
makeLenses ''Atom

instance Show Atom where { show (Atom s p) = (if s then "+" else "-") ++ show p }

atom'name :: Lens' Atom PredName
atom'name = atom'pred.pred'spred.spred'name
atom'args :: Lens' Atom [Term]
atom'args = atom'pred.pred'spred.spred'args

opposite :: Atom -> Atom -> Bool
opposite a1 a2 = a1^.atom'sign /= a2^.atom'sign && a1^.atom'name == a2^.atom'name

-- negated Conjunctive Normal Form
newtype OrClause = OrClause { _orClause'atoms :: [Atom] } deriving(Show,Ord,Eq)
makeLenses ''OrClause
newtype NotAndForm = NotAndForm { _notAndForm'orClauses :: [OrClause] } deriving(Show,Ord,Eq,Semigroup,Monoid)
makeLenses ''NotAndForm

-- Disjunctive Normal Form
newtype AndClause = AndClause { _andClause'atoms :: [Atom] } deriving(Ord,Eq)
makeLenses ''AndClause
newtype OrForm = OrForm { _orForm'andClauses :: [AndClause] } deriving(Ord,Eq,Semigroup,Monoid)
makeLenses ''OrForm

toNotAndForm :: OrForm -> NotAndForm
toNotAndForm (OrForm cla) = NotAndForm (map notAndClause cla)

toOrForm :: NotAndForm -> OrForm
toOrForm (NotAndForm cla) = OrForm (map notOrClause cla)

notOrClause (OrClause atoms) = AndClause (atoms & traverse.atom'sign %~ not)
notAndClause (AndClause atoms) = OrClause (atoms & traverse.atom'sign %~ not)

filterSign :: Bool -> AndClause -> [Pred]
filterSign s = toListOf (andClause'atoms.traverse.filtered (\a -> a^.atom'sign == s).atom'pred)

instance Show OrForm where
  show f = unlines $ map show $ f^.orForm'andClauses
instance Show AndClause where
  show c = intercalate " /\\ " $ map show (c^.andClause'atoms)

sumOr (OrForm x) (OrForm y) = OrForm (Ordered.union x y)
prodOr (OrForm fa) (OrForm fb) = OrForm $ Ordered.nubSort [AndClause (Ordered.union ca cb) | AndClause ca <- fa, AndClause cb <- fb]
  
dnf :: Skolem.Form -> OrForm
dnf (Skolem.PosAtom p) = OrForm [AndClause [Atom True p]]
dnf (Skolem.NegAtom p) = OrForm [AndClause [Atom False p]]
dnf (Skolem.Or x) = foldl sumOr (OrForm []) (map dnf x)
dnf (Skolem.And x) = foldl prodOr (OrForm [AndClause []]) (map dnf x)

simplify :: OrForm -> OrForm
simplify (OrForm x) =
  let
    subAnd (AndClause cx) (AndClause cy) = Ordered.subset cx cy
    nonTrivial  = filter (\c -> [] == Ordered.isect (filterSign True c) (filterSign False c)) x
    notSubsumed = filter (\c -> not $ any (\x -> x /= c && subAnd x c) x) nonTrivial
  in OrForm notSubsumed

isSubForm :: OrForm -> OrForm -> Bool
isSubForm a b = all (\c -> any (isInstance c) (b^.orForm'andClauses)) (a^.orForm'andClauses)

atom'runMGU :: (Atom,Atom) -> Valuation -> Maybe Valuation
atom'runMGU (a1,a2) val = do
  if (a1^.atom'sign) /= (a2^.atom'sign) then Nothing else return ()
  if (a1^.atom'name) /= (a2^.atom'name) then Nothing else return ()
  if length (a1^.atom'args) /= length (a2^.atom'args) then Nothing else return ()
  foldM (flip MGU.runMGU) val $ zip (a1^.atom'args) (a2^.atom'args)

andClause'runMGU :: (AndClause,AndClause) -> Valuation -> Maybe Valuation
andClause'runMGU (c1,c2) val = do
  if length (c1^.andClause'atoms) /= length (c2^.andClause'atoms) then Nothing else return ()
  foldM (flip atom'runMGU) val $ zip (c1^.andClause'atoms) (c2^.andClause'atoms) 

isInstance :: AndClause -> AndClause -> Bool
isInstance a b = andClause'runMGU (a,b) emptyValuation /= Nothing

---------------------------------------------------------------------

orForm'pred :: Traversal' OrForm Pred
orForm'pred = orForm'andClauses.traverse.andClause'atoms.traverse.atom'pred
orForm'term :: Traversal' OrForm Term
orForm'term = orForm'pred.pred'spred.spred'args.traverse

pred'arity :: Fold Pred (PredName,Int)
pred'arity g p@(PCustom pn args) = g (pn,length args) *> pure p
pred'arity g p = pure p

term'arity :: Fold Term (FunName,Int)
term'arity g t@(TFun fn args) = g (fn,length args) *> pure t
term'arity g t = pure t

eq l r = Atom True (PEq (TVar $ fromIntegral l) (TVar $ fromIntegral r));
neq l r = Atom False (PEq (TVar $ fromIntegral l) (TVar $ fromIntegral r));

appendEqAxioms :: OrForm -> OrForm
appendEqAxioms f = let {
    reflAxiom = OrClause [eq 0 0];
    symmAxiom = OrClause [neq 0 1, eq 1 0];
    transAxiom = OrClause [neq 0 1, neq 1 2, eq 0 2];
    congPred :: (PredName,Int) -> NotAndForm;
    congPred (n,c) = let { -- A 0..c  $0=$i and p($1..$c) => p($1..$0..$c)
      pred :: [Int] -> Pred;
      pred l = PCustom n (map (TVar . fromIntegral) l);
      x :: [Int] = [1..c];
    } in NotAndForm $ map (\v -> OrClause [neq 0 v, Atom False (pred x), Atom True (pred $ replace [v] [0] x)]) x;
    congFun :: (FunName,Int) -> NotAndForm;
    congFun (n,c) = let { -- A 0..c  $0=$i => f($1..$c)=f($1..$0..$c)
      term :: [Int] -> Term;
      term l = TFun n (map (TVar . fromIntegral) l);
      x :: [Int] = [1..c];
    } in NotAndForm $ map (\v -> OrClause [neq 0 v, Atom True (PEq (term x) (term $ replace [v] [0] x))]) x;
    congPredClauses :: NotAndForm = mconcat $ map congPred $ unique $ f^..orForm'pred.pred'arity;
    congFunClauses :: NotAndForm = mconcat $ map congFun $ unique $ f^..orForm'term.term'subterm.term'arity;
  } in toOrForm (NotAndForm [reflAxiom,symmAxiom,transAxiom] <> congPredClauses <> congFunClauses) <> f

