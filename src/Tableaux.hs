{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ViewPatterns #-}
module Tableaux(proveAxiomatic,proveBrand) where

import Prelude hiding(pred)
import Lib
import Proof(Proof,andClause'term)
import DNF
import Pred
import qualified Skolem
import LPO(lpo)
import qualified MGU
import qualified DiscTree
import DiscTree(match)
import Brand
import EqAxioms
import KBO(kbo)

import Control.Monad(mplus,mzero,MonadPlus,join,foldM,when)
import Control.Monad.State.Class(MonadState,get,put)
import qualified Control.Monad.Trans.Cont as ContM
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.Trans.Class(lift)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Set.Monad as SetM
import Control.Lens(makeLenses, Fold, Traversal, Traversal', (&), (%~), (.~), over, view, use, (.=), (%=),(^.),(^..))
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


type SelClause = ([Atom],Atom,[Atom],OrClauseCEE)

data TabState = TabState {
  _reductionOrder :: Int -> (Term,Term) -> Bool, -- a < b ?
  _clauses :: [OrClauseCEE],
  _clausesSelector :: Atom -> [SelClause],
  _nextVar :: VarName,
  -- we are limiting nodes, not vars, because it is possible to create an infinite branch of
  -- clauses without variables, see for example: (!p or !q) and (p or q)
  _nodesUsed, _nodesLimit :: Int,
  _ineq :: Set.Set Atom,
  _mguState :: Valuation, --_eq :: Set.Set (Term,Term)
  _usedClauses :: [OrClauseCEE],
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

allM :: [M a] -> M [a]
--allM = mapM branchM
allM [] = return []
allM [t] = branchM t >>= return.(:[])
allM tasks = do
  let n = length tasks
  used <- liftTab $ use nodesUsed
  limit <- liftTab $ use nodesLimit
  let perTask = (limit-used) `div` n
  let h:t = tasks
  join $ anyM [
    do {
      liftTab $ nodesLimit .= used + perTask;
      rh <- branchM h;
      liftTab $ nodesLimit .= limit;
      allM t >>= return.(rh:);
    },
    do {
      liftTab $ nodesLimit .= limit - (perTask+1);
      rt <- allM t;
      liftTab $ nodesLimit .= limit;
      branchM h >>= return.(:rt);
    }]


throw :: M a
throw = do
  lift $ lift $ lift $ lift $ failCount %= (+1)
  lift $ lift $ lift $ ExceptM.throwE ()

------------------------------------------------- 

allocVar :: M Term
allocVar = do
  vu <- liftTab $ use nextVar
  liftTab $ nextVar %= (+1)
  return (wrap $ TVar vu)

allocM :: VarName -> AllocM Term
allocM name = do
  varMap <- get
  case Map.lookup name varMap of
    Nothing -> do { t <- lift $ allocVar; put (Map.insert name t varMap); return t }
    Just t -> return t

atom'subst :: Traversal Atom Atom VarName Term
atom'subst = atom'args.traverse.term'subst

orClauseCEE'atom :: Traversal' OrClauseCEE Atom
orClauseCEE'atom f (OrClauseCEE atoms redAtoms derivation) = pure OrClauseCEE
  <*> (orClause'atoms.traverse) f atoms
  <*> (orClause'atoms.traverse) f redAtoms
  <*> (traverse.orClause'atoms.traverse) f derivation
orClauseCEE'subst :: Traversal OrClauseCEE OrClauseCEE VarName Term
orClauseCEE'subst = orClauseCEE'atom.atom'subst
orClause'term = orClause'atoms.traverse.atom'args.traverse

selClause'subst :: Traversal SelClause SelClause VarName Term
selClause'subst f (l,x,r,c) =
  pure (,,,) <*>
  (traverse.atom'subst) f l <*>
  atom'subst f x <*>
  (traverse.atom'subst) f r <*>
  orClauseCEE'subst f c

allocVars :: OrClauseCEE -> M [Atom]
allocVars cla = do
  (cla',_) <- StateM.runStateT (orClauseCEE'subst allocM cla) Map.empty
  mapM_ addIneq (cla'^.orClauseCEE'redAtoms.orClause'atoms)
  liftTab $ usedClauses %= (cla':)
  return $ cla'^.orClauseCEE'atoms.orClause'atoms

allocVars'SelClause :: SelClause -> M SelClause
allocVars'SelClause sc = do
  (sc'@(_,_,_,cla),_) <- StateM.runStateT (selClause'subst allocM sc) Map.empty
  liftTab $ usedClauses %= (cla:)
  return sc'

allocNode :: M ()
allocNode = do
  nu <- liftTab $ use nodesUsed
  nl <- liftTab $ use nodesLimit
  if nu >= nl then throw else do
    liftTab $ nodesUsed %= (+1)

withCtx :: String -> M a -> M a
--withCtx msg cont = liftTab (ctx %= (msg:)) >> cont
withCtx msg cont = cont

pushAndCont :: M ProofTree -> Atom -> M ProofTree
pushAndCont cont a = do
  liftBranch $ branch %= (a:)
  withCtx (show a) (showCtx >> cont) >>= return . Node a

start :: M ProofTree
start = do
  atoms <- (liftTab $ use $ clauses) >>= anyM >>= allocVars
  when (any (^.atom'sign) atoms) throw
  allM (map (pushAndCont expand) atoms) >>= return . Expand

expand :: M ProofTree
expand = do
  allocNode
  liftSearch $ totalNodeCount %= (+1)
  h:_ <- liftBranch $ use $ branch
  selector <- liftTab $ use clausesSelector
  ms <- liftTab $ use mguState
  let h' = h & atom'args.traverse %~ eval ms & atom'sign %~ not
  (l,x,r,_) <- (anyM $ selector h') >>= allocVars'SelClause
  bx <- branchM $ pushAndCont strong x
  b <- allM (map (pushAndCont weak) (l ++ r))
  let (bl,br) = splitAt (length l) b
  return $ Expand $ bl <> [bx] <> br

---------------------------------

validateIneq :: Atom -> M ()
validateIneq (Atom sign (unwrap -> PCustom redLTPredName [l,r])) = do
  s <- liftTab $ use mguState
  ord <- liftTab $ use reductionOrder
  varCount <- liftTab $ use nextVar >>= return.fromIntegral
  let (l',r') = (eval s l, eval s r)
  -- "l<r or C" => we need to ensure "l>=r" => if "l<r" throw
  if sign then
    when (ord varCount (l',r')) throw
  -- "l>=r or C" => we need to ensure "l<r" => if "l>r" or "l=r" throw
  else
    when (l' == r' || ord varCount (r',l')) throw

addEQ :: (Term,Term) -> M ()
addEQ lr = do
  s <- liftTab $ use mguState
  case MGU.runMGU lr s of { Nothing -> throw; Just s' -> liftTab $ mguState .= s' }
  lrs <- liftTab $ use ineq
  mapM_ validateIneq lrs

addIneq :: Atom -> M ()
addIneq a = case a of {
  -- "a!=b or C" => we need to ensure "a=b" => unify a and b
  Atom False (unwrap -> PCustom redEqPredName [l,r]) -> addEQ (l,r);
  _ -> do {
    liftTab $ ineq %= Set.insert a;
    validateIneq a
  }
}


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
    a1:a2:_ -> if not (opposite a1 a2) then throw else
        mapM addEQ (zip (a1^.atom'args) (a2^.atom'args)) >> (withCtx "STRONG" showCtx) >> return Strong

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

makeClausesSelector :: NotAndFormCEE -> (Atom -> [SelClause])
makeClausesSelector f = let { tree = DiscTree.build [(x^.atom'term,(l,x,r,cla)) |
    cla <- f^.notAndFormCEE'orClausesCEE,
    (l,x,r) <- select (cla^.orClauseCEE'atoms.orClause'atoms)]
  } in \a -> tree^..match (a^.atom'term)

{-makeClausesSelector f = let { x = [(l,x,r,cla) |
    cla <- f^.notAndFormCEE'orClausesCEE,
    (l,x,r) <- select (cla^.orClauseCEE'atoms.orClause'atoms)]
  } in \a -> x
-}

proveAxiomatic :: OrForm -> Int -> IO (Maybe Proof)
proveAxiomatic form = let {
  NotAndForm clauses = toNotAndForm (appendEqAxioms form);
  clauses' = map (\cla -> OrClauseCEE cla mempty [cla]) clauses
} in proveLoop (NotAndFormCEE clauses')

proveBrand :: OrForm -> Int -> IO (Maybe Proof)
proveBrand form n = do
  printE $ NotAndForm $ cee (toNotAndForm form) ^.. notAndFormCEE'orClausesCEE.traverse.orClauseCEE'atoms
  proveLoop (cee (toNotAndForm form)) n

emptyOrder :: Int -> (Term,Term) -> Bool
emptyOrder _ _ = False

lpoOrder :: Int -> (Term,Term) -> Bool
lpoOrder _ (l,r) = lpo l r

-- returns a DNF of terminal clauses which implies input form (and is always true)
prove :: NotAndFormCEE  -> Int -> IO (Maybe Proof, SearchState)
prove form nodesLimit = do
  let {
    -- negate the input form
    clausesSelector = makeClausesSelector form;
    initialState = TabState lpoOrder (form^.notAndFormCEE'orClausesCEE) clausesSelector 0 0 nodesLimit Set.empty Map.empty [] [];
    -- start with expand step
    runCont = ContM.runContT start return;
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
      return (Just $ toOrForm $ NotAndForm $ (s^..usedClauses.traverse.orClauseCEE'derivation.traverse) & traverse.orClause'term %~ ground . eval (s^.mguState), searchState)

proveLoop :: NotAndFormCEE -> Int -> IO (Maybe Proof)
proveLoop f limit = let
  rec f i = do
    t0 <- Clock.getTime Clock.ProcessCPUTime
    (res,searchState) <- prove f i
    return (force searchState)
    t1 <- Clock.getTime Clock.ProcessCPUTime
    printE (fromIntegral (searchState^.totalNodeCount)) -- / diffSeconds t1 t0)
    case res of {
      Nothing -> do {
        putStrLnE (show i ++ " -> " ++ show (searchState^.failCount));
        if i<limit then rec f (i+1) else putStrLnE "fail" >> return Nothing
      };
      Just x -> return (Just x)
    }
  in rec f 0
