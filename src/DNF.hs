{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedLabels #-}
module DNF(
  dnf, simplify, isSubForm,
  Atom(..), atom'sign, atom'pred, atom'name, atom'args, atom'term, opposite,
  OrForm(..), orForm'andClauses,
  AndClause(..), andClause'atoms,
  NotAndForm(..), notAndForm'orClauses,
  OrClause(..), orClause'atoms,
  notOrClause, notAndClause,
  toNotAndForm, toOrForm,
  fromProto, fromProto'File,
  toProto, toProto'Input,
) where

import Prelude hiding(pred)
import Pred
import qualified Skolem
import Lib
import qualified MGU
import qualified Proto.Tptp as T

import Form(freeVars'Formula,push,fromProto'Pred,toProto'Pred,NameIndex,M,RM,runM,runRM)
import qualified Data.Text as Text
import qualified Data.List.Ordered as Ordered
import Control.Monad(foldM,when)
import qualified Control.Monad.Trans.Reader as ReaderM
import Control.Lens
import Data.List(intercalate,find)
import Data.List.Utils (replace)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.ProtoLens(defMessage)

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

newtype NotAndForm = NotAndForm { _notAndForm'orClauses :: [OrClause] } deriving(Ord,Eq,Semigroup,Monoid)
makeLenses ''NotAndForm
instance Show NotAndForm where { show f = unlines $ map show $ f^.notAndForm'orClauses }

-- Disjunctive Normal Form
newtype AndClause = AndClause { _andClause'atoms :: [Atom] } deriving(Ord,Eq)
makeLenses ''AndClause
instance Show AndClause where { show c = intercalate " /\\ " $ map show (c^.andClause'atoms) }

newtype OrForm = OrForm { _orForm'andClauses :: [AndClause] } deriving(Ord,Eq,Semigroup,Monoid)
makeLenses ''OrForm
instance Show OrForm where { show f = unlines $ map show $ f^.orForm'andClauses }

toNotAndForm :: OrForm -> NotAndForm
toNotAndForm (OrForm cla) = NotAndForm (map notAndClause cla)

toOrForm :: NotAndForm -> OrForm
toOrForm (NotAndForm cla) = OrForm (map notOrClause cla)

notOrClause (OrClause atoms) = AndClause (atoms & traverse.atom'sign %~ not)
notAndClause (AndClause atoms) = OrClause (atoms & traverse.atom'sign %~ not)

filterSign :: Bool -> AndClause -> [Pred]
filterSign s = toListOf (andClause'atoms.traverse.filtered (\a -> a^.atom'sign == s).atom'pred)

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

isSubForm :: OrForm -> OrForm -> Maybe [AndClause]
isSubForm a b = mapM (\c -> find (isInstance c) (b^.orForm'andClauses)) (a^.orForm'andClauses)

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

-----------------------------------------------------

fromProto :: T.File -> NameIndex -> Either String (OrForm,NameIndex)
fromProto f ni = runM (fromProto'File f) ni

toProto :: OrForm -> NameIndex -> Either String T.File
toProto f ni = runRM (toProto'File f) ni

-----------------------------------------------------

fromProto'File :: T.File -> M OrForm
fromProto'File f = mapM fromProto'Input (f^. #input) >>= return . OrForm . map notOrClause

fromProto'Input :: T.Input -> M OrClause
fromProto'Input i = do
  let { freeVars = unique $ freeVars'Formula (i^. #formula) }
  when (i^. #language /= T.Input'CNF) (fail $ "unexpected language: " ++ show (i^. #language));
  case i^. #role of {
    T.Input'AXIOM -> return ();
    T.Input'PLAIN -> return ();
    T.Input'NEGATED_CONJECTURE -> return ();
    role@_ -> fail ("unexpected role: " ++ show role);
  }
  push freeVars (fromProto'Form (i^. #formula))

fromProto'Form :: T.Formula -> M OrClause
fromProto'Form f =
  case f^. #maybe'formula of
    Nothing -> fail "field missing"
    Just (T.Formula'Pred' pred) -> do {
      a <- fromProto'Atom f;
      return (OrClause [a]);
    }
    Just (T.Formula'Op op) -> do {
      case (op^. #type') of {
        T.Formula'Operator'OR -> mapM fromProto'Atom (op^. #args) >>= return.OrClause;
        T.Formula'Operator'FALSE -> return (OrClause []);
        _ -> do { a <- fromProto'Atom f; return (OrClause [a]) };
      }
    }
    Just (opType@_) -> fail ("unexpected operator type: " ++ show opType)

fromProto'Atom :: T.Formula -> M Atom
fromProto'Atom f =
  case f^. #maybe'formula of
    Nothing -> fail "field missing"
    Just (T.Formula'Op op) -> do {
      when (op^. #type' /= T.Formula'Operator'NEG) (fail $ "unexpected operator type: " ++ show (op^. #type'));
      when (length (op^. #args) /= 1) (fail "expected 1 arg");
      let { [f'] = op^. #args };
      a <- fromProto'Atom f';
      return (a & atom'sign %~ not);
    }
    Just (T.Formula'Pred' pred) -> fromProto'Pred pred >>= return . Atom True
    Just (formType@_) -> fail ("unexpected formula type: " ++ show formType)

toProto'File :: OrForm -> RM T.File
toProto'File (OrForm clauses) = do
  inputs <- mapM (toProto'Input.notAndClause) clauses
  return $ defMessage & #input .~ inputs

toProto'Input :: OrClause -> RM T.Input
toProto'Input (OrClause atoms) = do
  atoms' <- mapM toProto'Atom atoms 
  return $ defMessage
    & #language .~ T.Input'CNF
    & #role .~ T.Input'PLAIN
    & #formula .~ (defMessage
      & #maybe'formula .~ (Just $ T.Formula'Op $ defMessage
        & #type' .~ T.Formula'Operator'OR
        & #args .~ atoms'))

toProto'Atom :: Atom -> RM T.Formula
toProto'Atom (Atom sign pred) = do
  pred' <- toProto'Pred pred
  let fpred = defMessage & #maybe'formula .~ Just (T.Formula'Pred' pred')
  let op = defMessage & #type' .~ T.Formula'Operator'NEG & #args .~ [fpred]
  let fop = defMessage & #maybe'formula .~ Just (T.Formula'Op op)
  case sign of { True -> return fpred; False -> return fop }

