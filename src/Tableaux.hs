{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Tableaux(prove,proveLoop) where

import Prelude hiding(pred)
import Lib
import Proof(Pred(..),Atom(..),AllocState,Clause(..),Proof)
import qualified DNF
import DNF(Term(..))
import Skolem(Subst(..),PredName,FunName)
import LPO(lpo)
import qualified MGU(run,eval,State)
import Control.Monad(mplus,mzero,MonadPlus,join)
import Control.Monad.State.Class(MonadState,get,put)
import qualified Control.Monad.Trans.Cont as ContM
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.Trans.Class(lift)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Set.Monad as SetM
import Control.Lens (makeLenses, (^.), (%~), (.~), over, view, use, (.=), (%=))
import Data.List.Utils (replace)
import Data.List(sort,nub)
import Control.Concurrent

data TabState = TabState {
  _clauses :: [[Atom]],
  _varsUsed :: Int,
  -- we are limiting nodes, not vars, because it is possible to create an infinite branch of
  -- clauses without variables, see for example: (!p or !q) and (p or q)
  _nodesUsed, _nodesLimit :: Int,
  _mguState :: MGU.State, --_eq :: Set.Set (Term,Term)
  _usedClauses :: [Clause]
}
makeLenses ''TabState

data BranchState = BranchState {
  _branch :: [Atom],
  _ctx :: [String]
}
makeLenses ''BranchState

type M = StateM.StateT BranchState (StateM.StateT TabState (ExceptM.ExceptT () IO))
type AllocM = StateM.StateT AllocState M

allM :: MonadState s m => [m a] -> m [a]
allM tasks = do { s <- get; res <- mapM (put s >>) tasks; put s; return res }

anyM :: MonadPlus m => [m a] -> m a
anyM = foldl mplus mzero

{-anyM :: [M a] -> M a
anyM tasks = StateM.StateT (\branch -> StateM.StateT (\tab ->
  let
    run = \t -> ExceptM.runExceptT (StateM.runStateT (StateM.runStateT t branch) tab)
    res = map run tasks
    find [] = return $ Left ()
    find (h:t) = do { x <- h; case x of { Left _ -> find t; r@(Right _) -> return  r} }
  in ExceptM.ExceptT $ find res))
-}

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
  lift $ varsUsed %= (+1)
  return (TVar vu)

allocM :: Int -> AllocM Term
allocM name = do
  varMap <- get
  case Map.lookup name varMap of
    Nothing -> do { t <- lift $ allocVar; put (Map.insert name t varMap); return t }
    Just t -> return t

allocVars :: [Atom] -> M [Atom]
allocVars atoms = withCtx (show atoms) $ do
  (atoms2,m) <- StateM.runStateT (subst allocM atoms) Map.empty
  lift $ usedClauses %= (Clause atoms m:)
  return atoms2 

allocNode :: M ()
allocNode = do
  nu <- lift $ use nodesUsed
  nl <- lift $ use nodesLimit
  if nu >= nl then throw else lift $ nodesUsed %= (+1)


-- allocates fresh variables
anyClause :: ([Atom] -> M a) -> M a
anyClause cont = (lift $ use clauses) >>= anyM . map (\cla -> allocVars cla >>=  cont)

withCtx :: String -> M a -> M a
--withCtx msg cont = ctx %= (msg:) >> cont
withCtx msg cont = cont
pushAndCont :: M [()] -> Atom -> M [()]
pushAndCont cont a = branch %= (a:) >> withCtx (show a) cont

expand :: M [()]
expand = anyClause (allButOne (pushAndCont weak) (pushAndCont strong)) >>= return . join

addEQ :: (Term,Term) -> M ()
addEQ lr = do
  s <- lift $ use mguState
  case MGU.run lr s of { Nothing -> throw; Just s' -> lift $ mguState .= s' }

--------------------------------

--sleep = lift $ lift $ lift $ threadDelay 100000

showCtx :: M ()
showCtx = return ()
--showCtx = use ctx >>= (lift . lift . lift . print)

strong :: M [()]
strong = withCtx "strong" $ do
  allocNode
  BranchState path _ <- get
  showCtx
  --lift $ lift $ lift $ print $ "strong " ++ show path
  case path of
    [a] -> expand
    a:b:_ -> do
      case (a,b) of
        (NegAtom (Pred n1 r), PosAtom (Pred n2 s)) | n1 == n2 -> mapM addEQ (zip r s) >> return []
        (PosAtom (Pred n1 r), NegAtom (Pred n2 s)) | n1 == n2 -> mapM addEQ (zip r s) >> return []
        _ -> throw
    [] -> throw

weak :: M [()]
weak = withCtx "weak" $ do
  allocNode
  BranchState path _ <- get
  anyM [
    case path of {
      NegAtom (Pred n1 s):t -> anyM [mapM addEQ (zip r s) >> return [] | PosAtom (Pred n2 r) <- t, n1 == n2];
      PosAtom (Pred n1 s):t -> anyM [mapM addEQ (zip r s) >> return [] | NegAtom (Pred n2 r) <- t, n1 == n2];
      _ -> throw
    },
    expand]

--------------------------------

eqPred :: Term -> Term -> Pred
eqPred l r = Pred 0 [l,r]

convPred :: DNF.Pred -> Pred
convPred p = case p of
  DNF.PCustom n x -> Pred (n+1) x
  DNF.PEq l r -> eqPred l r

convCla :: DNF.Cla -> [Atom]
convCla cla = (map (PosAtom . convPred) (SetM.toList $ DNF.pos cla)) ++ (map (NegAtom . convPred) (SetM.toList $  DNF.neg cla))

class CollectPredNames a where
  collectPredNames :: a -> [(PredName,Int)]
instance (CollectPredNames a) => CollectPredNames [a] where
  collectPredNames l = join $ map collectPredNames l
instance CollectPredNames Atom where
  collectPredNames (PosAtom p) = collectPredNames p
  collectPredNames (NegAtom p) = collectPredNames p
instance CollectPredNames Pred where
  collectPredNames (Pred 0 _) = []
  collectPredNames (Pred n x) = [(n,length x)]

class CollectFunNames a where
  collectFunNames :: a -> [(FunName,Int)]
instance (CollectFunNames a) => CollectFunNames [a] where
  collectFunNames l = join $ map collectFunNames l
instance CollectFunNames Atom where
  collectFunNames (PosAtom p) = collectFunNames p
  collectFunNames (NegAtom p) = collectFunNames p
instance CollectFunNames Pred where
  collectFunNames (Pred _ x) = collectFunNames x
instance CollectFunNames Term where
  collectFunNames (TVar _) = []
  collectFunNames (TFun f x) = [(f,length x)]

convForm :: DNF.Form -> [[Atom]]
convForm form = do
  let {
    clauses = map (map neg . convCla) (SetM.toList $ DNF.cla form);
    eq l r = PosAtom (eqPred (TVar l) (TVar r));
    neq l r = NegAtom (eqPred (TVar l) (TVar r));
    refl = [eq 0 0]; -- E $0!=$0
    symm = [eq 0 1, neq 1 0]; -- E E $0=$1 and $1!=$0
    trans = [eq 0 1, eq 1 2, neq 0 2]; -- EEE $0=$1 and $1=$2 and $0!=$2
    congPred (n,c) = let { -- E 0..c  $0=$i and p($1..$i..$c) and !p($1..$c)
      pred l = Pred n (map TVar l);
      x = [1..c];
    } in map (\v -> [eq 0 v, PosAtom (pred x), NegAtom (pred $ replace [v] [0] x)]) x;
    congFun (n,c) = let { -- E 0..c  $0=$i and f($1..$i..$c)!=f($1..$c)
      term l = TFun n (map TVar l);
      x = [1..c];
    } in map (\v -> [eq 0 v, NegAtom (eqPred (term x) (term $ replace [v] [0] x))]) x;
    congPredClauses :: [[Atom]] = join $ map congPred $ nub $ sort $ collectPredNames clauses;
    congFunClauses :: [[Atom]] = join $ map congFun $ nub $ sort $ collectFunNames clauses;
  } in [refl,symm,trans] ++ congPredClauses ++ congFunClauses ++ clauses

neg :: Atom -> Atom
neg (PosAtom p) = NegAtom p
neg (NegAtom p) = PosAtom p

finalSubst :: MGU.State -> Clause -> Clause
finalSubst mgus (Clause atoms as) = Clause atoms (Map.map (MGU.eval mgus) as)

prove :: DNF.Form -> Int -> IO (Maybe Proof)
prove form nodesLimit = do
  let {
    -- negate the input form
    clauses = convForm form;
    initialState = TabState clauses 0 0 nodesLimit Map.empty [];
    -- start with expand step
    runBranch = StateM.runStateT expand (BranchState [] []);
    runTab = StateM.runStateT runBranch initialState;
    runExcept = ExceptM.runExceptT runTab;
  }
  --print clauses
  res <- runExcept
  return $ case res of
    Left () -> Nothing
    Right (_,s) -> Just $ map (finalSubst $ s^.mguState) (s^.usedClauses)

proveLoop :: DNF.Form -> Int -> IO (Maybe Proof)
proveLoop f limit = let
  rec f i = do
    res <- prove f i
    case res of {
      Nothing -> do {
        print i;
        if i<limit then rec f (i+1) else putStrLn "fail" >> return Nothing
      };
      Just x -> return (Just x)
    }
  in rec f 0
