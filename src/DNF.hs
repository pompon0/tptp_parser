{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module DNF(
  dnf, simplify, isSubForm,
  Atom(..), atom'sign, atom'pred, atom'name, atom'args, atom'term, opposite,
  OrForm(..), orForm'andClauses,
  AndClause(..), andClause'atoms,
  NotAndForm(..), notAndForm'orClauses,
  OrClause(..), orClause'atoms,
  notOrClause, notAndClause,
  toNotAndForm, toOrForm,
) where

import Prelude hiding(pred)
import Pred
import qualified Skolem
import Lib
import qualified MGU
import qualified Data.List.Ordered as Ordered
import Control.Monad(foldM)
import Control.Lens(Traversal',Lens',Iso',Fold,filtered,makeLenses,(&),(%~),dimap,from,(^..),(^.),toListOf)
import Data.List(intercalate)
import Data.List.Utils (replace)
import qualified Data.Set as Set

data Atom = Atom { _atom'sign :: Bool, _atom'pred :: Pred } deriving(Eq,Ord)
makeLenses ''Atom

instance Show Atom where { show (Atom s p) = (if s then "+" else "-") ++ show p }

atom'name :: Lens' Atom PredName
atom'name = atom'pred.pred'spred.spred'name
atom'args :: Lens' Atom [Term]
atom'args = atom'pred.pred'spred.spred'args

opposite :: Atom -> Atom -> Bool
opposite a1 a2 = a1^.atom'sign /= a2^.atom'sign && a1^.atom'name == a2^.atom'name

atom'term :: Iso' Atom Term
atom'term = dimap atomToTerm (fmap termToAtom)
atomToTerm a = wrap $ TFun (if a^.atom'sign then 1 else 0) [wrap $ TFun (fromIntegral $ a^.atom'name) (a^.atom'args)]
termToAtom (unwrap -> TFun sign [unwrap -> TFun pn args]) = Atom (sign==1) ((SPred (fromIntegral pn) args)^.from pred'spred)

-- negated Conjunctive Normal Form
newtype OrClause = OrClause { _orClause'atoms :: [Atom] } deriving(Ord,Eq,Semigroup,Monoid)
makeLenses ''OrClause
instance Show OrClause where { show c = intercalate " \\/ " $ map show (c^.orClause'atoms) }

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

