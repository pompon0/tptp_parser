{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Brand(
  cee,
  OrClauseCEE(..), orClauseCEE'atoms, orClauseCEE'redAtoms, orClauseCEE'derivation,
  NotAndFormCEE(..), notAndFormCEE'orClausesCEE,
  redNEQ, redLT, redLE,
) where

import Lib
import Pred
import DNF
import Control.Lens
import Control.Monad.Trans.State as StateM
import Data.Semigroup(Max(..))

redNEQ l r = Atom False (SPred redEQPredName [l,r]^.from pred'spred)
redLT l r = Atom True (SPred redLTPredName [l,r]^.from pred'spred)
redLE l r = Atom False (SPred redLTPredName [r,l]^.from pred'spred)

-- const
data OrClauseCEE = OrClauseCEE {
  _orClauseCEE'atoms :: OrClause,
  _orClauseCEE'redAtoms :: OrClause,
  _orClauseCEE'derivation :: [OrClause] } deriving(Eq,Ord)
makeLenses ''OrClauseCEE

instance Show OrClauseCEE where
  show (OrClauseCEE atoms redAtoms derivation)
    = unlines (show atoms : show redAtoms : map (\c -> "  "++show c) derivation)

oc = OrClause
occ = OrClauseCEE

instance Semigroup OrClauseCEE where
  OrClauseCEE a r d <> OrClauseCEE a' r' d' = occ (a <> a') (r <> r') (d <> d')
instance Monoid OrClauseCEE where
  mempty = occ mempty mempty mempty

newtype NotAndFormCEE = NotAndFormCEE {
  _notAndFormCEE'orClausesCEE :: [OrClauseCEE] } deriving(Ord,Eq,Semigroup,Monoid,Show)
makeLenses ''NotAndFormCEE

eq s t = Atom True (wrap $ PEq s t)
neq s t = Atom False (wrap $ PEq s t) 

symm :: OrClause -> [OrClauseCEE]
symm cla = let { 
  symm'Atom a@(Atom True (unwrap -> PEq s t)) = [
    occ (oc [a]) mempty [],
    occ (oc [eq t s]) mempty [oc [a & atom'sign %~ not, eq t s]]];
  symm'Atom a@(Atom False (unwrap -> PEq s@(unwrap -> TVar _) t@(unwrap -> TFun _ _))) = [
    occ (oc [neq t s]) mempty [oc [a & atom'sign %~ not, neq t s]]];
  symm'Atom a = [occ (oc [a]) mempty []];
} in foldr (\atom acc -> [x <> y | x <- symm'Atom atom, y <- acc]) [occ mempty mempty [cla]] (cla^.orClause'atoms)

type M = StateM.State VarName

mt :: OrClauseCEE -> OrClauseCEE
mt cla = let {
  -- returns a var to use instead of the term
  -- and a partial clause to append to the resulting clause
  mt'Term :: Term -> M (Term,OrClauseCEE);
  mt'Term t@(unwrap -> TVar _) = return (t,mempty);
  mt'Term ft@(unwrap -> TFun fn args) = do {
    (args',atoms) <- mapM mt'Term args >>= return.unzip;
    zn <- id <+= 1;
    let { l = wrap $ TFun fn args' };
    let { r = wrap $ TVar zn };
    return (r,
      occ (oc [neq l r]) mempty [
        -- t_i = x_i => f(t_i) = f(x_i)
        oc (eq ft l : map (\(t,x) -> neq t x) (zip args args')),
        -- f(t_i) = f(x_i) and f(x_i) = z => f(t_i) = z
        oc [neq ft l, neq l r, eq ft r]
      ] <> mconcat atoms);
  };
  -- returns a partial clause corresponding to the atom
  mt'Atom :: Atom -> M OrClauseCEE;
  mt'Atom a@(Atom _ (unwrap -> PCustom _ args)) = do {
    (args',atoms) <- mapM mt'Term args >>= return.unzip;
    zn <- id <+= 1;
    let { a' = a & atom'args .~ args' };
    let { na = a & atom'sign %~ not };
    return $ occ (oc [a']) mempty [
        -- t_i = x_i and p(t_i) => p(x_i)
        oc (a' : na : map (\(t,x) -> neq t x) (zip args args'))
      ] <> mconcat atoms;
  };
  mt'Atom a@(Atom sign (unwrap -> PEq l@(unwrap -> TFun fn args) r)) = do {
    (args',atoms) <- mapM mt'Term args >>= return.unzip;
    (r',r'atoms) <- mt'Term r;
    let { l' = wrap $ TFun fn args' };
    let { a' = Atom sign $ wrap $ PEq l' r' };
    let { na = a & atom'sign %~ not };
    return $ occ (oc [a']) mempty [
        -- t_i = x_i  =>  f(t_i) = f(x_i)
        oc (eq l l' : map (\(t,x) -> neq t x) (zip args args')),
        -- f(t_i) = f(x_i) and r = x and f(t_i) = r  =>  f(x_i) = x
        oc [a', na, neq l l', neq r r']
      ] <> r'atoms <> mconcat atoms;
  };
  mt'Atom a@(Atom sign (unwrap -> PEq l@(unwrap -> TVar _) r@(unwrap -> TFun _ _))) = do {
    (r',r'atoms) <- mt'Term r;
    let { a' = Atom sign $ wrap $ PEq l r' };
    let { na = a & atom'sign %~ not };
    return $ occ (oc [a']) mempty [
      -- l = r and r = r'  =>  l = r'
      oc [a', na, neq r r']
    ] <> r'atoms;
  };
  mt'Atom a@(Atom sign (unwrap -> PEq (unwrap -> TVar _) (unwrap -> TVar _))) = return $ occ (oc [a]) mempty mempty;
  var (unwrap -> TVar vn) = Just vn;
  var _ = Nothing;
  maxVar = foldl max (-1) $ cla^..orClauseCEE'atoms.orClause'atoms.traverse.atom'args.traverse.term'subterm.to var.traverse;
  (res,_) = StateM.runState (mapM mt'Atom (cla^.orClauseCEE'atoms.orClause'atoms) >>= return.mconcat) maxVar;
} in OrClauseCEE mempty mempty (cla^.orClauseCEE'derivation) <> res 


g :: OrClauseCEE -> OrClauseCEE
g cla = let {
  g'Atom :: Atom -> Maybe Atom;
  g'Atom (Atom False (unwrap -> PEq x@(unwrap -> TVar _) y@(unwrap -> TVar _))) = Just $ redNEQ x y;
  g'Atom (Atom True (unwrap -> PEq s t)) = Just $ redLE s t;
  g'Atom (Atom False (unwrap -> PEq p@(unwrap -> TFun _ _) y)) = Just $ redLT p y;
  g'Atom _ = Nothing;
} in cla & orClauseCEE'redAtoms .~ oc (cla^..orClauseCEE'atoms.orClause'atoms.traverse.to g'Atom.traverse)


cee'OrClause :: OrClause -> NotAndFormCEE
cee'OrClause cla = NotAndFormCEE $ symm cla >>= return . g . mt

--TODO: convert it to (OrForm -> OrFormCEE)
cee :: NotAndForm -> NotAndFormCEE
cee (NotAndForm cla) = let {
  x = wrap $ TVar 0;
  refl = oc [Atom True (wrap $ PEq x x)];
  reflAxiom = OrClauseCEE refl mempty [refl];
} in NotAndFormCEE [reflAxiom] <> mconcat (map cee'OrClause cla)
