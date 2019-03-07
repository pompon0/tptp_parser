{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module LazyParam(prove,proveLoop) where

import Lib
import DNF
import Pred
import LPO(lpo)
import qualified MGU
import qualified Proof
import qualified Tableaux
import Proof(andClause'term)


import Control.Monad(mplus,mzero,MonadPlus,join)
import Control.Monad.State.Class(MonadState,get,put)
import qualified Control.Monad.Trans.Cont as ContM
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.Trans.Class(lift)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Set.Monad as SetM
import Control.Lens(Traversal',Lens',makeLenses, (&), (%~), (.~), over, view, use, (.=), (%=))
import Control.DeepSeq(NFData,force)
import GHC.Generics (Generic)
import qualified System.Clock as Clock

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
  _nodesUsed, _nodesLimit :: Int,
  _ineq :: Set.Set (Term,Term),
  _mguState :: Valuation, --_eq :: Set.Set (Term,Term)
  _usedClauses :: [AndClause],
  
  _choices :: [String]
}
makeLenses ''TabState

data BranchState = BranchState {
  _branch :: [Atom],
  _ctx :: [String]
}
makeLenses ''BranchState

type M = ContM.ContT ProofTree (StateM.StateT BranchState (StateM.StateT TabState (ExceptM.ExceptT () (StateM.StateT SearchState IO))))

liftBranch = lift
liftTab = liftBranch.lift
liftSearch = liftTab.lift.lift

{-anyM :: [a] -> M a
anyM choices_ = ContM.ContT $ \cont -> StateM.StateT $ \branch -> StateM.StateT $ \tab ->
    let
      wrap (i,a) = do { liftTab $ choices %= ((show i ++ "/" ++ show (length choices_)):); showCtx; return a }
      run t = ExceptM.runExceptT (StateM.runStateT (StateM.runStateT (ContM.runContT t cont) branch) tab)
      res = map (run.wrap) $ zip [1..] choices_
      find :: [Output] -> Output
      find [] = do { putStrLnE "out of options"; return (Left ()) }
      find (h:t) = do { x<-h; case x of { Left () -> find t; x@(Right _) -> do { putStrLnE "got it"; return x } } }
    in ExceptM.ExceptT (find res)
-}
anyM :: (MonadPlus m) => [a] -> ContM.ContT r m a
anyM choices = ContM.ContT (\cont -> foldl mplus mzero (map cont choices))

allM :: (MonadState s m) => [m ProofTree] -> m ProofTree
allM tasks = do { s <- get; res <- mapM (put s >>) tasks; put s; return (Expand res) }

throw :: M a
throw = do
  lift $ lift $ lift $ lift $ failCount %= (+1)
  lift $ lift $ lift $ ExceptM.throwE ()

allButOne :: (a -> M ProofTree) -> (a -> M ProofTree) -> [a] -> M ProofTree
allButOne all one tasks = do
  (x,r) <- anyM (select tasks)
  allM (one x : map all r)

------------------------------------------------- 

allocVar :: M Term
allocVar = do
  vu <- liftTab $ use nextVar
  liftTab $ nextVar %= (+1)
  return (TVar vu)

type AllocM = StateM.StateT (Map.Map VarName Term) M

allocM :: VarName -> AllocM Term
allocM name = do
  varMap <- get
  case Map.lookup name varMap of
    Nothing -> do { t <- lift $ allocVar; put (Map.insert name t varMap); return t }
    Just t -> return t

orClause'subst = orClause'atoms.traverse.atom'pred.pred'spred.spred'args.traverse.term'subst

allocVars :: OrClause -> M [Atom]
allocVars cla = do
  (cla2,_) <- StateM.runStateT (orClause'subst allocM cla) emptyValuation
  liftTab $ usedClauses %= (notOrClause cla2:)
  return $ cla2^.orClause'atoms

allocNode :: M ()
allocNode = do
  nu <- liftTab $ use nodesUsed
  nl <- liftTab $ use nodesLimit
  if nu >= nl then throw else liftTab $ nodesUsed %= (+1)

-- allocates fresh variables
anyClause :: M [Atom]
anyClause = (liftTab $ use $ clauses.notAndForm'orClauses) >>= anyM >>= allocVars

applySymmAxiom :: (Term,Term) -> M (Term,Term)
applySymmAxiom (l,r) = join $ anyM [
  return (l,r),
  do
    liftTab $ usedClauses %= ((notOrClause $ OrClause [Atom False (PEq l r), Atom True (PEq r l)]):)
    return (r,l)]

withCtx msg cont = cont
--withCtx :: String -> M a -> M a
--withCtx msg cont = do
--  ctx %= (msg:) >> cont

showCtx = return ()
--showCtx :: M ()
--showCtx = do
--  nu <- liftTab $ use nodesUsed
--  nl <- liftTab $ use nodesLimit
--  ch <- liftTab $ use choices
--  c <- use ctx
--  putStrLnE (show nu ++ "/" ++ show nl ++ "  " ++ show (reverse ch) ++ "  " ++ show (reverse c))

pushAndCont :: M ProofTree -> Atom -> M ProofTree
pushAndCont cont a = branch %= (a:) >> withCtx (show a) cont >>= return . Node a

expand :: M ProofTree
expand = do
  liftSearch $ totalNodeCount %= (+1)
  anyClause >>= allButOne (pushAndCont weak) (pushAndCont strong)

--------------------------------

validateLT :: (Term,Term) -> M ()
validateLT (l,r) = do
  s <- liftTab $ use mguState
  if lpo (eval s r) (eval s l) then throw else return ()

addEQ :: (Term,Term) -> M ()
addEQ lr = withCtx ("addEQ " ++ show lr) $ do
  showCtx
  s <- liftTab $ use mguState
  case MGU.runMGU lr s of { Nothing -> throw; Just s' -> liftTab $ mguState .= s' }
  lrs <- liftTab $ use ineq
  mapM_ validateLT lrs
addLT :: (Term,Term) -> M ()
addLT lr = do
  liftTab $ ineq %= Set.insert lr
  validateLT lr

--------------------------------

lazyEq :: [Term] -> [Term] -> M ProofTree
lazyEq r s = do
  -- do the allocation first to early exit if not enough resources present
  v <- mapM (\_ -> allocVar) r
  mapM_ addEQ (zip v r)
  -- WARNING: zip will truncate the longer list if lengths mismatch
  -- TODO: throw an error instead
  liftSearch $ totalNodeCount %= (+1)
  allM $ map (\(s',v') -> pushAndCont weak (Atom False (PEq s' v'))) (zip s v) 

axiomCongFun :: (Term,Term) -> M ()
axiomCongFun (t1@(TFun n1 a1), t2@(TFun n2 a2)) = do
  let diff = filter (\(x,y) -> x/=y) (zip a1 a2)
  mapM axiomCongFun diff
  let axiom = OrClause $ map (\(x,y) -> Atom False (PEq x y)) diff ++ [Atom True (PEq t1 t2)]
  --TODO: add warning if !=1
  if length diff == 0 then return () else
    liftTab $ usedClauses %= (notOrClause axiom:)
axiomCongFun _ = return ()

pred'args :: Lens' Pred [Term]
pred'args = pred'spred.spred'args

axiomCongPred :: (Pred,Pred) -> M ()
axiomCongPred (p1,p2) = do
  let diff = filter (\(x,y) -> x/=y) $ zip (p1^.pred'args) (p2^.pred'args)
  mapM axiomCongFun diff
  let axiom = OrClause $ map (\(x,y) -> Atom False (PEq x y)) diff ++ [Atom False p1, Atom True p2]
  if length diff == 0 then return () else
    liftTab $ usedClauses %= (notOrClause axiom:)

data Swap s a = Swap { runSwap :: [(a,s)], runId :: [a] }

instance Functor (Swap p) where { fmap f = (pure f <*>) }
instance Applicative (Swap s) where
  pure x = Swap [] [x]
  Swap uf vf <*> Swap ux vx = Swap ([(f x,s) | (f,s) <- uf, x <- vx] ++ [(f x,s) | f <- vf, (x,s) <- ux]) [f x | f <- vf, x <- vx]
instance Semigroup (Swap s a) where
  Swap ua va <> Swap ub vb = Swap (ua <> ub) (va <> vb)

swap :: Term -> Term -> Swap Term Term
swap t' t@(TVar _) = pure t
swap t' t@(TFun name args) = Swap [(t',t)] [] <> (pure (TFun name) <*> traverse (swap t') args)

atom'term = atom'pred.pred'spred.spred'args.traverse

-- S || \Gamma, L[p], z~r
-- S || \Gamma, L[p], f(s)~r
strongLEq :: Atom -> (Term,Term) -> M ProofTree
strongLEq aLp (l,r) = do
  w <- allocVar
  (aLw,p) <- anyM (runSwap $ atom'term (swap w) aLp)
  axiomCongPred (aLw^.atom'pred, aLp^.atom'pred)
  case l of
    z@(TVar _) -> do {
      addEQ (p,z);
      addLT (w,z);
      liftSearch $ totalNodeCount %= (+1);
      allM $ map (pushAndCont weak) [aLw, Atom False (PEq r w)];
    }
    TFun f s -> do {
      v <- mapM (\_ -> allocVar) s;
      addEQ (p,TFun f v);
      addLT (w,TFun f v);
      let { subgoals = aLw : map (\(x,y) -> Atom False (PEq x y)) (zip (r:s) (w:v)) };
      liftSearch $ totalNodeCount %= (+1);
      allM $ map (pushAndCont weak) subgoals;
    }

-- S || \Gamma, l~r, L[f(s)]
strongEqL :: (Term,Term) -> Atom -> M ProofTree
strongEqL (l,r) aLp = do
  w <- allocVar
  (aLw,p) <- anyM (runSwap $ atom'term (swap w) aLp)
  axiomCongPred (aLw^.atom'pred, aLp^.atom'pred)
  case p of
    (TFun f s) -> do {
      v <- mapM (\_ -> allocVar) s;
      addEQ (TFun f v,l);
      addLT (r,l);
      addEQ (r,w);
      let { subgoals = aLw : map (\(x,y) -> Atom False (PEq x y)) (zip s v) };
      liftSearch $ totalNodeCount %= (+1);
      allM $ map (pushAndCont weak) subgoals;
    }
    _ -> throw

strong :: M ProofTree
strong = withCtx "strong" $ do
  allocNode
  path <- use branch
  showCtx
  case path of
    [] -> throw
    [a] -> expand
    a:b:_ -> join $ anyM [
      (case (a,b) of
        -- S || \Gamma,!P[r],P[s]
        -- S || \Gamma,P[r],!P[s]
        (Atom x1 (PCustom n1 r), Atom x2 (PCustom n2 s)) | x1/=x2, n1 == n2 -> lazyEq r s
        _ -> throw),
      (case (a,b) of
        -- not sure if non-paramodulation strong step for equality predicate is needed
        -- TODO: verify that against the proof
        -- TODO: verify if swapping r* with s* is needed
        (Atom x1 (PEq r1 r2), Atom x2 (PEq s1 s2)) | x1/=x2 -> do {
            (s1',s2') <- applySymmAxiom (s1,s2);
            lazyEq [r1,r2] [s1',s2']
          }
        _ -> throw),
      (case (a,b) of
        -- S || \Gamma, L[p], z~r
        -- S || \Gamma, L[p], f(s)~r
        (Atom True (PEq l r), aLp) -> applySymmAxiom (l,r) >>= strongLEq aLp
        _ -> throw),
      (case (a,b) of
        -- S || \Gamma, l~r, L[f(s)]
        (aLp, Atom True (PEq l r)) -> applySymmAxiom (l,r) >>= (\lr -> strongEqL lr aLp)
        _ -> throw)]

weakLEq :: Atom -> (Term,Term) -> M ProofTree
weakLEq aLp (l,r) = do
  w <- allocVar
  (aLw,p) <- anyM (runSwap $ atom'term (swap w) aLp)
  axiomCongPred (aLw^.atom'pred, aLp^.atom'pred)
  addEQ (p,l)
  addLT (r,l)
  addEQ (r,w)
  pushAndCont weak aLw

weak :: M ProofTree
weak = withCtx "weak" $ do
  allocNode
  path <- use branch
  join $ anyM [
    -- S || \Gamma, s!~t
    case path of { DNF.Atom False (PEq l r):_ -> addEQ (l,r) >> return Weak; _ -> throw },
    expand,
    -- S || \Gamma L[p],\Delta,l~r
    case path of {
      (DNF.Atom True (PEq l r):t) -> join $ anyM [applySymmAxiom (l,r) >>= weakLEq aLp | aLp <- t]; _ -> throw },
    -- S || \Gamma l~r,\Delta,L[p]
    case path of { (aLp:t) -> join $ anyM [applySymmAxiom (l,r) >>= weakLEq aLp | DNF.Atom True (PEq l r) <- t]; _ -> throw },
    -- S || \Gamma,!P[r],\Delta,P[s]
    -- S || \Gamma,P[r],\Delta,!P[s]
    case path of {
      DNF.Atom x1 (PCustom n1 s):t -> join $ anyM [mapM addEQ (zip r s) >> return Weak | DNF.Atom x2 (PCustom n2 r) <- t, x1/=x2, n1 == n2];
      DNF.Atom x1 (PEq l r):t -> join $ anyM [do {
          (l',r') <- applySymmAxiom (l,r);
          mapM addEQ (zip [l2,r2] [l',r']);
          return Weak
        } | DNF.Atom x2 (PEq l2 r2) <- t, x1/=x2];
      _ -> throw
    }]

--------------------------------

prove :: OrForm -> Int -> IO (Maybe Proof.Proof, SearchState)
prove form nodesLimit = do
  let {
    -- negate the input form
    clauses = toNotAndForm form;
    initialState = TabState clauses 0 0 nodesLimit Set.empty Map.empty [] [];
    -- start with expand step
    runCont = ContM.runContT expand return;
    runBranch = StateM.runStateT runCont (BranchState [] []);
    runTab = StateM.runStateT runBranch initialState;
    runExcept = ExceptM.runExceptT runTab;
    runSearch = StateM.runStateT runExcept (SearchState 0 0);
  }
  --print clauses
  (res,searchState) <- runSearch
  case res of
    Left () -> return (Nothing,searchState)
    Right ((proofTree,bs),s) -> do
      print proofTree
      return (Just $ s^.usedClauses & traverse.andClause'term %~ eval (s^.mguState), searchState) 

proveLoop :: OrForm -> Int -> IO (Maybe Proof.Proof)
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
