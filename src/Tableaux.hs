{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Tableaux(prove,proveLoop) where

import Prelude hiding(pred)
import Lib
import Proof(Proof,andClause'term)
import DNF
import Pred
import qualified Skolem
import LPO(lpo)
import qualified MGU
import Control.Monad(mplus,mzero,MonadPlus,join,foldM)
import Control.Monad.State.Class(MonadState,get,put)
import qualified Control.Monad.Trans.Cont as ContM
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.Trans.Class(lift)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Set.Monad as SetM
import Control.Lens(makeLenses, Fold, Traversal, Traversal', (&), (%~), (.~), over, view, use, (.=), (%=))
import Data.List.Utils (replace)
import Data.List(sort,nub)
import Control.Concurrent
import qualified System.Clock as Clock
import Control.DeepSeq(NFData,force)
import GHC.Generics (Generic)

data ProofTree = Strong | Weak | Expand [ProofTree] | Node Atom ProofTree

indent s = "  " ++ s

showTree :: ProofTree -> [String]
showTree Strong = ["Strong"]
showTree Weak = ["Weak"]
showTree (Node a t) = show a : map indent (showTree t)
showTree (Expand t) = join (map showTree t)

instance Show ProofTree where { show t = unlines (showTree t) }

data SearchState = SearchState {
  _failCount :: Int,
  _totalNodeCount :: Int
} deriving(Generic,NFData)
makeLenses ''SearchState

data TabState = TabState {
  _clauses :: NotAndForm,
  _nextVar :: VarName,
  -- we are limiting nodes, not vars, because it is possible to create an infinite branch of
  -- clauses without variables, see for example: (!p or !q) and (p or q)
  _nodesUsed, _nodesLimit :: Int,
  _mguState :: Valuation, --_eq :: Set.Set (Term,Term)
  _usedClauses :: [AndClause],
  _ctx :: [String]
}
makeLenses ''TabState

data BranchState = BranchState {
  _branch :: [Atom]
}
makeLenses ''BranchState

type M = ContM.ContT ProofTree (StateM.StateT BranchState (StateM.StateT TabState (ExceptM.ExceptT () (StateM.StateT SearchState IO))))
type AllocM = StateM.StateT Valuation M

liftBranch = lift
liftTab = liftBranch.lift
liftSearch = liftTab.lift.lift

anyM :: (MonadPlus m) => [a] -> ContM.ContT r m a
anyM choices = ContM.ContT (\cont -> foldl mplus mzero (map cont choices))

branchM :: (MonadState s m) => m a -> m a
branchM task = do { s <- get; r <- task; put s; return r }

throw :: M a
throw = do
  lift $ lift $ lift $ lift $ failCount %= (+1)
  lift $ lift $ lift $ ExceptM.throwE ()

allButOne :: (a -> M ProofTree) -> (a -> M ProofTree) -> [a] -> M ProofTree
allButOne all one tasks = do
  (l,x,r) <- anyM (select tasks)
  bx <- branchM $ one x
  bl <- mapM (branchM.all) l
  br <- mapM (branchM.all) r
  return $ Expand $ bl <> [bx] <> br

------------------------------------------------- 

allocVar :: M Term
allocVar = do
  vu <- liftTab $ use nextVar
  liftTab $ nextVar %= (+1)
  return (TVar vu)

allocM :: VarName -> AllocM Term
allocM name = do
  varMap <- get
  case Map.lookup name varMap of
    Nothing -> do { t <- lift $ allocVar; put (Map.insert name t varMap); return t }
    Just t -> return t

orClause'subst = orClause'atoms.traverse.atom'pred.pred'spred.spred'args.traverse.term'subst

allocVars :: OrClause -> M [Atom]
allocVars cla = do
  (cla2,_) <- StateM.runStateT (orClause'subst allocM cla) Map.empty
  liftTab $ usedClauses %= (notOrClause cla2:)
  return $ cla2^.orClause'atoms

allocNode :: M ()
allocNode = do
  nu <- liftTab $ use nodesUsed
  nl <- liftTab $ use nodesLimit
  if nu >= nl then throw else do
    liftTab $ nodesUsed %= (+1)


-- allocates fresh variables
anyClause :: M [Atom]
anyClause = (liftTab $ use $ clauses.notAndForm'orClauses) >>= anyM >>= allocVars

withCtx :: String -> M a -> M a
--withCtx msg cont = liftTab (ctx %= (msg:)) >> cont
withCtx msg cont = cont

pushAndCont :: M ProofTree -> Atom -> M ProofTree
pushAndCont cont a = do
  liftBranch $ branch %= (a:)
  withCtx (show a) (showCtx >> cont) >>= return . Node a

expand :: M ProofTree
expand = do
  allocNode
  liftSearch $ totalNodeCount %= (+1)
  atoms <- anyClause
  withCtx (show $ OrClause atoms) $ allButOne (pushAndCont weak) (pushAndCont strong) atoms

addEQ :: (Term,Term) -> M ()
addEQ lr = do
  s <- liftTab $ use mguState
  case MGU.runMGU lr s of { Nothing -> throw; Just s' -> liftTab $ mguState .= s' }

--------------------------------

--sleep = lift $ lift $ lift $ threadDelay 100000

showCtx :: M ()
showCtx = return ()
{-showCtx = do
  c <- liftTab $ use ctx
  if length c<=20 then printE (reverse c) else return ()
-}
strong :: M ProofTree
strong = do
  path <- liftBranch $ use branch
  showCtx
  --lift $ lift $ lift $ print $ "strong " ++ show path
  case path of
    [a] -> expand
    a1:a2:_ -> if not (opposite a1 a2) then throw else
        mapM addEQ (zip (a1^.atom'args) (a2^.atom'args)) >> (withCtx "STRONG" showCtx) >> return Strong
    [] -> throw

weak :: M ProofTree
weak = do
  path <- liftBranch $ use branch
  join $ anyM [
    case path of {
      a1:t -> join $ anyM [mapM addEQ (zip (a1^.atom'args) (a2^.atom'args)) >> (withCtx "WEAK" showCtx) >> return Weak | a2 <- t, opposite a1 a2];
      _ -> throw
    },
    expand]

--------------------------------

-- returns a DNF of terminal clauses which implies input form (and is always true)
prove :: OrForm -> Int -> IO (Maybe Proof, SearchState)
prove form nodesLimit = do
  let {
    -- negate the input form
    clauses = toNotAndForm (appendEqAxioms form);
    initialState = TabState clauses 0 0 nodesLimit Map.empty [] [];
    -- start with expand step
    runCont = ContM.runContT expand return;
    runBranch = StateM.runStateT runCont (BranchState []);
    runTab = StateM.runStateT runBranch initialState;
    runExcept = ExceptM.runExceptT runTab;
    runSearch = StateM.runStateT runExcept (SearchState 0 0);
  }
  --print clauses
  (res,searchState) <- runSearch
  case res of
    Left () -> return (Nothing,searchState)
    Right ((proofTree,bs),s) -> do
      printE proofTree
      return (Just $ OrForm $ s^.usedClauses & traverse.andClause'term %~ eval (s^.mguState), searchState)

proveLoop :: OrForm -> Int -> IO (Maybe Proof)
proveLoop f limit = let
  rec f i = do
    t0 <- Clock.getTime Clock.ProcessCPUTime
    (res,searchState) <- prove f i
    return (force searchState)
    t1 <- Clock.getTime Clock.ProcessCPUTime
    printE (fromIntegral (searchState^.totalNodeCount) / diffSeconds t1 t0)
    case res of {
      Nothing -> do {
        putStrLnE (show i ++ " -> " ++ show (searchState^.failCount));
        if i<limit then rec f (i+1) else putStrLnE "fail" >> return Nothing
      };
      Just x -> return (Just x)
    }
  in rec f 0
