{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Brand where

import Lib
import Pred
import DNF
import Control.Lens
import Control.Monad.Trans.State as StateM
import Data.Semigroup(Max(..))

-- reduction atoms
data RedAtom = Red'NEQ Term Term | Red'LT Term Term | Red'LE Term Term deriving(Eq,Ord)

-- const
data OrClauseCEE = OrClauseCEE {
  _orClauseCEE'atoms :: [Atom],
  _orClauseCEE'redAtoms :: [RedAtom] } deriving(Eq,Ord)
makeLenses ''OrClauseCEE

newtype NotAndFormCEE = NotAndFormCEE {
  _notAndFormCEE'orClauses :: [OrClauseCEE] } deriving(Ord,Eq,Semigroup,Monoid)

makeLenses ''NotAndFormCEE

symm :: OrClause -> [OrClause]
symm cla = let { 
  symm'Atom a@(Atom True (unwrap -> PEq s t)) = [a, Atom True (wrap $ PEq t s)];
  symm'Atom a@(Atom False (unwrap -> PEq s@(unwrap -> TVar _) t@(unwrap -> TFun _ _))) = [Atom False (wrap $ PEq s t)];
  symm'Atom a = [a];
} in foldr (\atom acc -> [OrClause [x] <> y | x <- symm'Atom atom, y <- acc]) [mempty] (cla^.orClause'atoms)

type M = StateM.State VarName

mt :: OrClause -> OrClause
mt cla = let {
  mt'Term :: Term -> M (Term,OrClause);
  mt'Term t@(unwrap -> TVar _) = return (t,mempty);
  mt'Term (unwrap -> TFun fn args) = do {
    (args',atoms) <- mapM mt'Term args >>= return.unzip;
    zn <- id <+= 1;
    let { l = wrap $ TFun fn args' };
    let { r = wrap $ TVar zn };
    return (r, OrClause [Atom False (wrap $ PEq l r)] <> mconcat atoms);
  };
  mt'Pred :: Pred -> M (Pred,OrClause);
  mt'Pred (unwrap -> PCustom pn args) = do {
    (args',atoms) <- mapM mt'Term args >>= return.unzip;
    zn <- id <+= 1;
    return (wrap $ PCustom pn args', mconcat atoms);
  };
  mt'Pred (unwrap -> PEq (unwrap -> TFun fn args) r) = do {
    (args',atoms) <- mapM mt'Term args >>= return.unzip;
    (r',r'atoms) <- mt'Term r;
    let { l' = wrap $ TFun fn args' };
    return (wrap $ PEq l' r', r'atoms <> mconcat atoms);
  };
  mt'Pred eqXY = return (eqXY,mempty);
  mt'Atom :: Atom -> M OrClause;
  mt'Atom atom = do {
    (p',atoms) <- mt'Pred (atom^.atom'pred);
    return $ OrClause [atom & atom'pred .~ p'] <> atoms;
  };
  var (unwrap -> TVar vn) = Just vn;
  var _ = Nothing;
  maxVar = foldl max (-1) $ cla^..orClause'atoms.traverse.atom'args.traverse.term'subterm.to var.traverse;
  (res,_) = StateM.runState (mapM mt'Atom (cla^.orClause'atoms) >>= return.mconcat) maxVar;
} in res 

g :: OrClause -> OrClauseCEE
g (OrClause atoms) = let {
  g'Atom :: Atom -> [RedAtom];
  g'Atom (Atom False (unwrap -> PEq x@(unwrap -> TVar _) y@(unwrap -> TVar _))) = [Red'NEQ x y];
  g'Atom (Atom True (unwrap -> PEq s t)) = [Red'LE s t];
  g'Atom (Atom False (unwrap -> PEq p@(unwrap -> TFun _ _) y)) = [Red'LT p y];
  g'Atom _ = [];
} in OrClauseCEE atoms (atoms >>= g'Atom)

cee'OrClause :: OrClause -> NotAndFormCEE
cee'OrClause cla = NotAndFormCEE $ map (g.mt) (symm cla)

--TODO: convert it to (OrForm -> OrFormCEE)
cee :: NotAndForm -> NotAndFormCEE
cee (NotAndForm cla) = mconcat $ map cee'OrClause cla
