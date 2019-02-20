{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Tableaux(prove,proveLoop,finalSubst) where

import Prelude hiding(pred)
import Lib
import Proof(Valuation,Clause(..),Proof)
import DNF
import qualified Skolem
import Skolem(Term(..),Pred(..),SPred(..),term'subst,term'subterm,pred'spred,spred'args,spred'name)
import LPO(lpo)
import qualified MGU(run,eval,State)
import Control.Monad(mplus,mzero,MonadPlus,join,foldM)
import Control.Monad.State.Class(MonadState,get,put)
import qualified Control.Monad.Trans.Cont as ContM
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.Trans.Class(lift)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Set.Monad as SetM
import Control.Lens(makeLenses, Fold, Traversal', (&), (%~), (.~), over, view, use, (.=), (%=))
import Data.List.Utils (replace)
import Data.List(sort,nub)
import Control.Concurrent

data SearchState = SearchState {
  _failCount :: Int
}
makeLenses ''SearchState

data TabState = TabState {
  _clauses :: NotAndForm,
  _nextVar :: VarName,
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

type M = StateM.StateT BranchState (StateM.StateT TabState (ExceptM.ExceptT () (StateM.StateT SearchState IO)))
type AllocM = StateM.StateT Valuation M

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
throw = do
  lift $ lift $ lift $ failCount %= (+1)
  lift $ lift $ ExceptM.throwE ()

allButOne :: (a -> M b) -> (a -> M b) -> [a] -> M [b]
allButOne all one [] = throw
allButOne all one (h:t) = anyM ([
  allM (one h : map all t),
  do { rt <- allButOne all one t; rh <- allM [all h]; return $ rh ++ rt}] )

------------------------------------------------- 

allocVar :: M Term
allocVar = do
  vu <- lift $ use nextVar
  lift $ nextVar %= (+1)
  return (TVar vu)

allocM :: VarName -> AllocM Term
allocM name = do
  varMap <- get
  case Map.lookup name varMap of
    Nothing -> do { t <- lift $ allocVar; put (Map.insert name t varMap); return t }
    Just t -> return t

orClause'subst = orClause'atoms.traverse.atom'pred.pred'spred.spred'args.traverse.term'subst

allocVars :: OrClause -> M [Atom]
allocVars cla = withCtx (show cla) $ do
  (cla2,m) <- StateM.runStateT (orClause'subst allocM cla) Map.empty
  lift $ usedClauses %= (Clause (notOrClause cla) m:)
  return $ cla2^.orClause'atoms

allocNode :: M ()
allocNode = do
  nu <- lift $ use nodesUsed
  nl <- lift $ use nodesLimit
  if nu >= nl then throw else lift $ nodesUsed %= (+1)


-- allocates fresh variables
anyClause :: ([Atom] -> M a) -> M a
anyClause cont = (lift $ use (clauses.notAndForm'orClauses)) >>= anyM . map (\cla -> allocVars cla >>= cont)

withCtx :: String -> M a -> M a
--withCtx msg cont = ctx %= (msg:) >> cont
withCtx msg cont = cont
pushAndCont :: M [()] -> Atom -> M [()]
pushAndCont cont a = branch %= (a:) >> withCtx (show a) cont

expand :: M [()]
expand = withCtx "expand" $ do
  showCtx
  anyClause (allButOne (pushAndCont weak) (pushAndCont strong)) >>= return . join

addEQ :: (Term,Term) -> M ()
addEQ lr = withCtx (show lr) $ do
  showCtx
  s <- lift $ use mguState
  case MGU.run lr s of { Nothing -> throw; Just s' -> lift $ mguState .= s' }

--------------------------------

--sleep = lift $ lift $ lift $ threadDelay 100000

showCtx :: M ()
showCtx = return ()
--showCtx = use ctx >>= printE

strong :: M [()]
strong = withCtx "strong" $ do
  allocNode
  BranchState path _ <- get
  showCtx
  --lift $ lift $ lift $ print $ "strong " ++ show path
  case path of
    [a] -> expand
    a1:a2:_ -> if not (opposite a1 a2) then throw else
        mapM addEQ (zip (a1^.atom'args) (a2^.atom'args)) >> return []
    [] -> throw

weak :: M [()]
weak = withCtx "weak" $ do
  allocNode
  BranchState path _ <- get
  anyM [
    case path of {
      a1:t -> anyM [mapM addEQ (zip (a1^.atom'args) (a2^.atom'args)) >> return [] | a2 <- t, opposite a1 a2];
      _ -> throw
    },
    expand]

--------------------------------

notAndForm'pred :: Traversal' NotAndForm Pred
notAndForm'pred = notAndForm'orClauses.traverse.orClause'atoms.traverse.atom'pred
notAndForm'term :: Traversal' NotAndForm Term
notAndForm'term = notAndForm'pred.pred'spred.spred'args.traverse

pred'arity :: Fold Pred (PredName,Int)
pred'arity g p@(PCustom pn args) = g (pn,length args) *> pure p
pred'arity g p = pure p

term'arity :: Fold Term (FunName,Int)
term'arity g t@(TFun fn args) = g (fn,length args) *> pure t
term'arity g t = pure t

-- converts DNF form to prove, into CNF form to refute
convForm :: OrForm -> NotAndForm
convForm form = do
  let {
    clauses = toNotAndForm form;
    eq l r = Atom True (PEq (TVar $ fromIntegral l) (TVar $ fromIntegral r));
    neq l r = Atom False (PEq (TVar $ fromIntegral l) (TVar $ fromIntegral r));
    refl = OrClause [eq 0 0]; 
    symm = OrClause [neq 0 1, eq 1 0]; 
    trans = OrClause [neq 0 1, neq 1 2, eq 0 2]; 
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
    congPredClauses :: NotAndForm = mconcat $ map congPred $ nub $ sort $ clauses^..notAndForm'pred.pred'arity;
    congFunClauses :: NotAndForm = mconcat $ map congFun $ nub $ sort $ clauses^..notAndForm'term.term'subterm.term'arity;
  } in NotAndForm [refl,symm,trans] <> congPredClauses <> congFunClauses <> clauses

finalSubst :: MGU.State -> Clause -> Clause
finalSubst mgus (Clause atoms as) = Clause atoms (Map.map (MGU.eval mgus) as)

-- returns a DNF of terminal clauses which implies input form (and is always true)
prove :: OrForm -> Int -> IO (Maybe Proof, Int)
prove form nodesLimit = do
  let {
    -- negate the input form
    clauses = convForm form;
    initialState = TabState clauses 0 0 nodesLimit Map.empty [];
    -- start with expand step
    runBranch = StateM.runStateT expand (BranchState [] []);
    runTab = StateM.runStateT runBranch initialState;
    runExcept = ExceptM.runExceptT runTab;
    runSearch = StateM.runStateT runExcept (SearchState 0);
  }
  --print clauses
  (res,searchState) <- runSearch
  return $ case res of
    Left () -> (Nothing,_failCount searchState)
    Right (_,s) -> (Just $ map (finalSubst $ s^.mguState) (s^.usedClauses), searchState^.failCount)

proveLoop :: OrForm -> Int -> IO (Maybe Proof)
proveLoop f limit = let
  rec f i = do
    (res,failCount) <- prove f i
    case res of {
      Nothing -> do {
        putStrLnE (show i ++ " -> " ++ show failCount);
        if i<limit then rec f (i+1) else putStrLnE "fail" >> return Nothing
      };
      Just x -> return (Just x)
    }
  in rec f 0
