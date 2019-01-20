{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LazyParam where

import DNF(Term(..),Pred(..))
import Skolem(Subst(..))
import LPO(lpo)
import Control.Monad(mplus,mzero,MonadPlus,join)
import Control.Monad.State.Class(MonadState,get,put)
import qualified Control.Monad.Trans.Cont as ContM
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.Trans.Class(lift)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Lens (makeLenses, (^.), (%~), (.~), over, view, use, (.=), (%=))

data Atom = PosAtom Pred | NegAtom Pred

instance Subst Atom where
  subst f (PosAtom p) = subst f p >>= return . PosAtom
  subst f (NegAtom p) = subst f p >>= return . NegAtom

data TabState = TabState {
  _clauses :: [[Atom]],
  _varsUsed, _varsLimit :: Int,
  _eq,_ineq :: Set.Set (Term,Term)
}
makeLenses ''TabState

data BranchState = BranchState {
  _branch :: [Atom]
}
makeLenses ''BranchState

type M = StateM.StateT BranchState (StateM.StateT TabState (ExceptM.Except ()))

allM :: MonadState s m => [m a] -> m [a]
allM tasks = do { s <- get; res <- mapM (put s >>) tasks; put s; return res }

anyM :: MonadPlus m => [m a] -> m a
anyM = foldl mplus mzero

throw :: M a
throw = lift $ lift $ ExceptM.throwE ()

allButOne :: (a -> M b) -> (a -> M b) -> [a] -> M [b]
allButOne all one [] = throw
allButOne all one (h:t) = anyM ([
  allM (one h : map all t),
  do { rt <- allButOne all one t; rh <- allM [all h]; return $ rh ++ rt}] )

------------------------------------------------- 

allocVar :: M Term
allocVar = do
  vu <- lift $ use varsUsed
  vl <- lift $ use varsLimit
  if vu >= vl then throw else do
    lift $ varsUsed %= (+1)
    return (TVar vu)

type AllocM = StateM.StateT (Map.Map Int Term) M

allocM :: Int -> AllocM Term
allocM name = do
  varMap <- get
  case Map.lookup name varMap of
    Nothing -> do { t <- lift $ allocVar; put (Map.insert name t varMap); return t }
    Just t -> return t

allocVars :: [Atom] -> M [Atom]
allocVars atoms = StateM.evalStateT (subst allocM atoms) Map.empty

-- allocates fresh variables
anyClause :: ([Atom] -> M a) -> M a
anyClause cont = (lift $ use clauses) >>= anyM . map (\cla -> allocVars cla >>= cont)

pushAndCont :: M [()] -> Atom -> M [()]
pushAndCont cont a = branch %= (a:) >> cont

expand :: M [()]
expand = anyClause (allButOne (pushAndCont weak) (pushAndCont strong)) >>= return . join


addEQ :: (Term,Term) -> M ()
addEQ = error ""
addLT :: (Term,Term) -> M ()
addLT = error ""

lazyEq :: [Term] -> [Term] -> M [()]
lazyEq r s = do
  -- do the allocation first to early exit if not enough resources present
  v <- mapM (\_ -> allocVar) r
  mapM_ addEQ (zip v r)
  -- WARNING: zip will truncate the longer list if lengths mismatch
  -- TODO: throw an error instead
  allM (map (\(s',v') -> pushAndCont weak (NegAtom (PEq s' v'))) (zip s v)) >>= return . join


strong :: M [()]
strong = do
  BranchState path <- get
  case path of
    a:b:_ -> do
      case (a,b) of
        (NegAtom (PCustom n1 r), PosAtom (PCustom n2 s)) | n1 == n2 -> lazyEq r s
        (PosAtom (PCustom n1 r), NegAtom (PCustom n2 s)) | n1 == n2 -> lazyEq r s
        -- not sure if non-paramodulation strong step for equality predicate is needed
        -- TODO: verify that against the proof
        (NegAtom (PEq r1 r2), PosAtom (PEq s1 s2)) -> lazyEq [r1,r2] [s1,s2]
        (PosAtom (PEq r1 r2), NegAtom (PEq s1 s2)) -> lazyEq [r1,r2] [s1,s2]
        (pL, PosAtom (PEq (TVar z) r)) -> error ""
        (pL, PosAtom (PEq (TFun f a) r)) -> error ""
        (PosAtom (PEq l r), pL) -> error ""
        _ -> throw
    _ -> throw

weak :: M [()]
weak = error ""

{-
===========================================

addEQ :: (Term,Term) -> M ()
addLT :: (Term,Term) -> M ()
getPath :: M [Atom]

============================================




weak :: M ()
weak = do
-}
