{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module LazyParam(prove,proveLoop) where

import Lib
import DNF
import Pred
import LPO(lpo)
import KBO(kbo)
import qualified MGU
import qualified Proof
import qualified Tableaux
import Proof(andClause'term)
import qualified LazyParamTree as Tree
import qualified Graph
import qualified DiscTree
import DiscTree(match)
import qualified ShallowIndex

import Control.Monad(mplus,mzero,MonadPlus,join,when)
import Control.Monad.State.Class(MonadState,get,put)
import qualified Control.Monad.Trans.Cont as ContM
import qualified Control.Monad.Trans.State.Lazy as StateM
import qualified Control.Monad.Trans.Except as ExceptM
import Control.Monad.Trans.Class(lift)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Set.Monad as SetM
import Control.Lens(Traversal',Lens',Fold,makeLenses, (&), (%~), (.~), over, view, use, (.=), (%=), (^.),(^..))
import Control.DeepSeq(NFData,force)
import GHC.Generics (Generic)
import qualified System.Clock as Clock

data SearchState = SearchState {
  _failCount :: Int,
  _totalNodeCount :: Int
} deriving(Generic,NFData)
makeLenses ''SearchState

data TabState = TabState {
  _reductionOrder :: Int -> (Term,Term) -> Bool, -- a < b ?
  _clauses :: NotAndForm,
  _nextVar :: VarName,
  _nodesUsed, _nodesLimit :: Int,
  _ineq :: Set.Set (Term,Term),
  _mguState :: Valuation
}
makeLenses ''TabState

data BranchState = BranchState {
  _branch :: [Atom],
  _branchAtomSelector :: DiscTree.Tree Atom,
  _branchSubtermIndex :: ShallowIndex.SubtermIndex Atom,
  _ctx :: [String]
}
makeLenses ''BranchState

type M = ContM.ContT Tree.Node (StateM.StateT BranchState (StateM.StateT TabState (ExceptM.ExceptT () (StateM.StateT SearchState IO))))

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

allButOne :: (a -> M b) -> (a -> M b) -> [a] -> M [b]
allButOne all one tasks = do
  (l,x,r) <- anyM (select tasks)
  bx <- branchM $ one x
  bl <- mapM (branchM.all) l
  br <- mapM (branchM.all) r
  return (bl <> [bx] <> br)

------------------------------------------------- 

allocVar :: M Term
allocVar = do
  vu <- liftTab $ use nextVar
  liftTab $ nextVar %= (+1)
  return (wrap $ TVar vu)

type AllocM = StateM.StateT (Map.Map VarName Term) M

allocM :: VarName -> AllocM Term
allocM name = do
  varMap <- get
  case Map.lookup name varMap of
    Nothing -> do { t <- lift $ allocVar; put (Map.insert name t varMap); return t }
    Just t -> return t

pred'name = pred'spred.spred'name
orClause'subst = orClause'atoms.traverse.atom'args.traverse.term'subst

allocVars :: OrClause -> M [Atom]
allocVars cla = do
  (cla2,_) <- StateM.runStateT (orClause'subst allocM cla) emptyValuation
  return $ cla2^.orClause'atoms

allocNode :: M ()
allocNode = do
  nu <- liftTab $ use nodesUsed
  nl <- liftTab $ use nodesLimit
  if nu >= nl then throw else liftTab $ nodesUsed %= (+1)

-- allocates fresh variables
anyClause :: M [Atom]
anyClause = (liftTab $ use $ clauses.notAndForm'orClauses) >>= anyM >>= allocVars

applySymmAxiom :: Atom -> (Atom -> M Tree.Node) -> M Tree.Node
applySymmAxiom a@(Atom x p) cont = case unwrap p of
  PEq l r -> join $ anyM [cont a, do
    let a' = Atom x (wrap $ PEq r l)
    n <- cont a' 
    return $ snd $ Tree.symm (Tree.negAtom a, n)]
  _ -> cont a

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

pushAndCont :: M Tree.Node -> Atom -> M (Atom,Tree.Node)
pushAndCont cont a = do
  s <- liftTab $ use mguState
  liftBranch $ branch %= (a:)
  liftBranch $ branchAtomSelector %= DiscTree.add ((a & atom'arg %~ eval s)^.atom'term, a)
  liftBranch $ branchSubtermIndex %= ShallowIndex.add (atom'arg ShallowIndex.swapAll a)
  withCtx (show a) cont >>= return.((,) a)

expand :: M Tree.Node
expand = do
  allocNode
  liftSearch $ totalNodeCount %= (+1)
  cla <- anyClause
  allButOne (pushAndCont weak) (pushAndCont strong) cla >>= return . Tree.expand

--------------------------------

validateLT :: (Term,Term) -> M ()
validateLT (l,r) = do
  s <- liftTab $ use mguState
  ord <- liftTab $ use reductionOrder
  varCount <- liftTab $ use nextVar
  if ord (fromIntegral varCount) (eval s r, eval s l) then throw else return ()

validateAcyclic :: M ()
validateAcyclic = do
  s <- liftTab $ use mguState
  edges :: [(Term,Term)] <- (liftTab $ use ineq) >>= return . map (\(l,r) -> (eval s l, eval s r)) . Set.toList
  if Graph.cyclic (Graph.toGraph edges) then throw else return ()

addEQ :: (Term,Term) -> M ()
addEQ lr = withCtx ("addEQ " ++ show lr) $ do
  showCtx
  s <- liftTab $ use mguState
  case MGU.runMGU lr s of { Nothing -> throw; Just s' -> liftTab $ mguState .= s' }
  lrs <- liftTab $ use ineq
  mapM_ validateLT lrs
  --validateAcyclic

addLT :: (Term,Term) -> M ()
addLT lr = do
  liftTab $ ineq %= Set.insert lr
  validateLT lr
  --validateAcyclic

--------------------------------

assertOpposite :: Atom -> Atom -> M ()
assertOpposite a b = if a^.atom'pred.pred'name /= b^.atom'pred.pred'name || a^.atom'sign==b^.atom'sign then throw else return ()

-- S || \Gamma,!P[r],P[s]
-- S || \Gamma,P[r],!P[s]
-- not sure if non-paramodulation strong step for equality predicate is needed
-- TODO: verify that against the proof
-- TODO: verify if swapping r* with s* is needed
strongPred :: Atom -> Atom -> M Tree.Node
strongPred a1 a2 =  do
  assertOpposite a1 a2
  let r = a1^.atom'args
  let s = a2^.atom'args
  v <- mapM (\_ -> allocVar) r
  mapM_ addEQ (zip v r)
  -- WARNING: zip will truncate the longer list if lengths mismatch
  -- TODO: throw an error instead
  liftSearch $ totalNodeCount %= (+1)
  ansr <- mapM (\(s',v') -> branchM $ pushAndCont weak (Atom False (wrap $ PEq s' v'))) (zip s v)
  return $ Tree.Node "strongPred" ((Tree.negAtom a1, Tree.Leaf):(Tree.negAtom a2, Tree.Leaf):ansr)

atom'arg :: Traversal' Atom Term
atom'arg = atom'args.traverse

assertEq :: Bool -> Atom -> M (Term,Term)
assertEq s (Atom x p) = if s/=x then throw else
  case unwrap p of { PEq l r -> return (l,r); _ -> throw }

-- S || \Gamma, L[p], z~r
-- S || \Gamma, L[p], f(s)~r
strongLEq :: Atom -> Atom -> M Tree.Node
strongLEq aLp alr = applySymmAxiom alr $ \alr -> do
  (l,r) <- assertEq True alr
  w <- allocVar
  (aL,p) <- anyM (ShallowIndex.build [atom'arg ShallowIndex.swapAll aLp]^..traverse.traverse)
  let aLw = aL w
  case unwrap l of
    TVar _ -> do {
      let { z = l };
      addEQ (p,z);
      addLT (w,z);
      liftSearch $ totalNodeCount %= (+1);
      anLw <- branchM $ pushAndCont weak aLw;
      anrw <- branchM $ pushAndCont weak $ Atom False $ wrap $ PEq r w;
      let { anpz = (Atom False $ wrap $ PEq p z, Tree.refl p) };
      let { anzr = (Atom False $ wrap $ PEq z r, Tree.Leaf) };
      let { anpw = foldl1 Tree.trans [anpz,anzr,anrw] };
      return $ Tree.atomCong aLp anLw anpw;
    }
    TFun f s -> do {
      let { fs = l };
      v <- mapM (\_ -> allocVar) s;
      let { fv = wrap $ TFun f v };
      addEQ (p,fv);
      addLT (w,fv);
      liftSearch $ totalNodeCount %= (+1);
      anLw <- branchM $ pushAndCont weak aLw;
      anrw <- branchM $ pushAndCont weak $ Atom False $ wrap $ PEq r w;
      ansv <- mapM (\(x,y) -> branchM $ pushAndCont weak $ Atom False $ wrap $ PEq x y) (zip s v);
      let { anpfv = (Atom False $ wrap $ PEq p fv, Tree.refl p) };
      let { anfvfs = Tree.symm (Tree.cong f ansv) };
      let { anfsr = (Atom False $ wrap $ PEq fs r, Tree.Leaf) };
      let { anpw = foldl1 Tree.trans [anpfv,anfvfs,anfsr,anrw] };
      return $ Tree.atomCong aLp anLw anpw;
    }

-- S || \Gamma, l~r, L[f(s)]
strongEqL :: Atom -> Atom -> M Tree.Node
strongEqL alr aLp = applySymmAxiom alr $ \alr -> do
  (l,r) <- assertEq True alr
  w <- allocVar
  (aL,p) <- anyM (ShallowIndex.build [atom'arg ShallowIndex.swapAll aLp]^..traverse.traverse)
  let aLw = aL w
  case unwrap p of
    TFun f s -> do {
      let { fs = p };
      v <- mapM (\_ -> allocVar) s;
      let { fv = wrap $ TFun f v };
      addEQ (fv,l);
      addLT (r,l);
      addEQ (r,w);
      liftSearch $ totalNodeCount %= (+1);
      anLw <- branchM $ pushAndCont weak aLw;
      ansv <- mapM (\(x,y) -> branchM $ pushAndCont weak $ Atom False $ wrap $ PEq x y) (zip s v);
      let { anpfv = Tree.cong f ansv };
      let { anfvl = (Atom False $ wrap $ PEq fv l, Tree.refl fv) };
      let { anlr = (Atom False $ wrap $ PEq l r, Tree.Leaf) };
      let { anrw = (Atom False $ wrap $ PEq r w, Tree.refl r) };
      let { anpw = foldl1 Tree.trans [anpfv,anfvl,anlr,anrw] };
      return $ Tree.atomCong aLp anLw anpw;
    }
    _ -> throw

strong :: M Tree.Node
strong = withCtx "strong" $ do
  allocNode
  path <- use branch
  showCtx
  case path of
    [] -> throw
    [a] -> expand
    a:b:_ -> join $ anyM [
      -- S || \Gamma,!P[r],P[s]
      -- S || \Gamma,P[r],!P[s]
      strongPred b a,
      -- S || \Gamma, L[p], z~r
      -- S || \Gamma, L[p], f(s)~r
      strongLEq b a,
      -- S || \Gamma, l~r, L[f(s)]
      strongEqL b a]

-- S || \Gamma L[p],\Delta,l~r
weakLEq :: Atom -> M Tree.Node
weakLEq alr = applySymmAxiom alr $ \alr -> do
  (l,r) <- assertEq True alr
  bsi <- liftBranch $ use branchSubtermIndex
  (aL,p) <- anyM (ShallowIndex.lookup l bsi)
  let aLp = aL p
  when (aLp == alr) throw
  w <- allocVar
  let aLw = aL w
  addEQ (p,l)
  addLT (r,l)
  addEQ (r,w)
  (root:_) <- liftBranch $ use branch
  anLw <- branchM $ pushAndCont weak aLw
  let { anpl = (Atom False $ wrap $ PEq p l, Tree.refl p) }
  let { anlr = (Atom False $ wrap $ PEq l r, Tree.Leaf) }
  let { anrw = (Atom False $ wrap $ PEq r w, Tree.refl p) }
  let { anpw = foldl1 Tree.trans [anpl,anlr,anrw] }
  return $ Tree.atomCong aLp anLw anpw

weak :: M Tree.Node
weak = withCtx "weak" $ do
  path <- liftBranch $ use branch
  bas <- liftBranch $ use branchAtomSelector
  join $ anyM [
    -- S || \Gamma, s!~t
    case path of {
      (aneq:_) -> do {
        (l,r) <- assertEq False aneq;
        addEQ (l,r);
        return (Tree.refl l);
      };
      _ -> throw
    },
    expand,
    -- S || \Gamma L[p],\Delta,l~r
    allocNode >> anyM path >>= weakLEq,
    -- S || \Gamma,!P[r],\Delta,P[s]
    -- S || \Gamma,P[r],\Delta,!P[s]
    case path of {
      (aPs:t) -> do {
        s <- liftTab $ use mguState;
        let { aPrList = bas^..match ((aPs & atom'arg %~ eval s & atom'sign %~ not)^.atom'term) };
        join $ anyM [ do
          assertOpposite aPs aPr
          applySymmAxiom aPs $ \aPs' -> do
            mapM addEQ (zip (aPr^.atom'args) (aPs'^.atom'args))
            return Tree.predWeak
        | aPr <- aPrList]; }; _ -> throw }]

--------------------------------

emptyOrder :: Int -> (Term,Term) -> Bool
emptyOrder _ _ = False

lpoOrder :: Int -> (Term,Term) -> Bool
lpoOrder _ (l,r) = lpo l r

prove :: OrForm -> Int -> IO (Maybe Proof.Proof, SearchState)
prove form nodesLimit = do
  let {
    -- negate the input form
    clauses = toNotAndForm form;
    initialState = TabState lpoOrder clauses 0 0 nodesLimit Set.empty Map.empty;
    -- start with expand step
    runCont = ContM.runContT expand return;
    runBranch = StateM.runStateT runCont (BranchState [] DiscTree.emptyTree ShallowIndex.emptySubtermIndex []);
    runTab = StateM.runStateT runBranch initialState;
    runExcept = ExceptM.runExceptT runTab;
    runSearch = StateM.runStateT runExcept (SearchState 0 0);
  }
  --print clauses
  (res,searchState) <- runSearch
  case res of
    Left () -> return (Nothing,searchState)
    Right ((proofTree,bs),s) -> do
      let proofTree' = proofTree & Tree.node'deepAtom.atom'arg %~ ground . eval (s^.mguState)
      printE proofTree'
      let proof = toOrForm $ NotAndForm (proofTree'^..(Tree.node'proof))
      --printE proof
      return (Just proof, searchState) 

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
