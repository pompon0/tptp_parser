{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LazyParam(prove,proveLoop) where

import qualified DNF
import DNF(Term(..),Pred(..))
import Skolem(Subst(..))
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

data Atom = PosAtom Pred | NegAtom Pred

instance Show Atom where
  show (PosAtom p) = "+" ++ show p
  show (NegAtom p) = "-" ++ show p

instance Subst Atom where
  subst f (PosAtom p) = subst f p >>= return . PosAtom
  subst f (NegAtom p) = subst f p >>= return . NegAtom

data TabState = TabState {
  _clauses :: [[Atom]],
  _varsUsed :: Int,
  _nodesUsed, _nodesLimit :: Int,
  _ineq :: Set.Set (Term,Term),
  _mguState :: MGU.State --_eq :: Set.Set (Term,Term)
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
allocVars atoms = do
  nu <- lift $ use nodesUsed
  nl <- lift $ use nodesLimit
  if nu + length atoms > nl then throw else do
    lift $ nodesUsed %= (+length atoms)
    StateM.evalStateT (subst allocM atoms) Map.empty

-- allocates fresh variables
anyClause :: ([Atom] -> M a) -> M a
anyClause cont = (lift $ use clauses) >>= anyM . map (\cla -> allocVars cla >>= cont)

pushAndCont :: M [()] -> Atom -> M [()]
pushAndCont cont a = branch %= (a:) >> cont

expand :: M [()]
expand = anyClause (allButOne (pushAndCont weak) (pushAndCont strong)) >>= return . join

--------------------------------

validateLT :: (Term,Term) -> M ()
validateLT (l,r) = do
  s <- lift $ use mguState
  if lpo (MGU.eval s r) (MGU.eval s l) then throw else return ()

addEQ :: (Term,Term) -> M ()
addEQ lr = do
  s <- lift $ use mguState
  case MGU.run lr s of { Nothing -> throw; Just s' -> lift $ mguState .= s' }
  lrs <- lift $ use ineq
  mapM_ validateLT lrs
addLT :: (Term,Term) -> M ()
addLT lr = do
  lift $ ineq %= Set.insert lr
  validateLT lr

--------------------------------

lazyEq :: [Term] -> [Term] -> M [()]
lazyEq r s = do
  -- do the allocation first to early exit if not enough resources present
  v <- mapM (\_ -> allocVar) r
  mapM_ addEQ (zip v r)
  -- WARNING: zip will truncate the longer list if lengths mismatch
  -- TODO: throw an error instead
  allM (map (\(s',v') -> pushAndCont weak (NegAtom (PEq s' v'))) (zip s v)) >>= return . join

class Extract s where
  extract :: s -> (s -> Term{-Var-} -> Term{-p-} -> M [()]) -> M [()]

instance Extract s => Extract [s] where
  extract [] cont = throw
  extract (h:t) cont = anyM [extract t (cont.(h:)), extract h (cont.(:t))]

instance Extract Term where
  extract (TVar _) cont = throw
  extract p@(TFun name args) cont = anyM [
    extract args (cont.(TFun name)),
    do { w <- allocVar; cont w w p }]

instance Extract Pred where
  extract (PEq l r) cont = anyM [
    extract l (cont.(\l' -> PEq l' r)),
    extract r (cont.PEq l)]
  extract (PCustom name args) cont = extract args (cont.PCustom name) 

instance Extract Atom where
  extract (PosAtom p) cont = extract p (cont.PosAtom)
  extract (NegAtom p) cont = extract p (cont.NegAtom)

-- S || \Gamma, L[p], z~r
-- S || \Gamma, L[p], f(s)~r
strongLEq :: Atom -> (Term,Term) -> M [()]
strongLEq aLp (l,r)= case l of
  z@(TVar _) -> extract aLp (\aLw w p -> do {
    addEQ (p,z);
    addLT (w,z);
    allM (map (pushAndCont weak) [aLw, NegAtom (PEq r w)]) >>= return.join
  })
  TFun f s -> extract aLp (\aLw w p -> do {
    v <- mapM (\_ -> allocVar) s;
    addEQ (p,TFun f v);
    addLT (w,TFun f v);
    let { subtasks = aLw : map (\(x,y) -> NegAtom (PEq x y)) (zip (r:s) (w:v)) };
    allM (map (pushAndCont weak) subtasks) >>= return.join
  })

-- S || \Gamma, l~r, L[f(s)]
strongEqL :: (Term,Term) -> Atom -> M [()]
strongEqL (l,r) aLp = extract aLp (\aLw w p -> case p of
  (TFun f s) -> do {
    v <- mapM (\_ -> allocVar) s;
    addEQ (TFun f v,l);
    addLT (r,l);
    addEQ (r,w);
    let { subtasks = aLw : map (\(x,y) -> NegAtom (PEq x y)) (zip (r:s) (w:v)) };
    allM (map (pushAndCont weak) subtasks) >>= return.join
  }
  _ -> throw)


strong :: M [()]
strong = do
  BranchState path <- get
  case path of
    [] -> throw
    [a] -> expand
    a:b:_ -> do
      case (a,b) of
        -- S || \Gamma,!P[r],P[s]
        -- S || \Gamma,P[r],!P[s]
        (NegAtom (PCustom n1 r), PosAtom (PCustom n2 s)) | n1 == n2 -> lazyEq r s
        (PosAtom (PCustom n1 r), NegAtom (PCustom n2 s)) | n1 == n2 -> lazyEq r s
        -- not sure if non-paramodulation strong step for equality predicate is needed
        -- TODO: verify that against the proof
        (NegAtom (PEq r1 r2), PosAtom (PEq s1 s2)) -> anyM [lazyEq [r1,r2] [s1,s2], lazyEq [r1,r2] [s2,s1]]
        (PosAtom (PEq r1 r2), NegAtom (PEq s1 s2)) -> anyM [lazyEq [r1,r2] [s1,s2], lazyEq [r1,r2] [s2,s1]]
        -- S || \Gamma, L[p], z~r
        -- S || \Gamma, L[p], f(s)~r
        (aLp, PosAtom (PEq l r)) -> anyM [strongLEq aLp (l,r), strongLEq aLp (r,l)]
        -- S || \Gamma, l~r, L[f(s)]
        (PosAtom (PEq l r), aLp) -> anyM [strongEqL (l,r) aLp, strongEqL (r,l) aLp]
        _ -> throw

weakLEq :: Atom -> (Term,Term) -> M [()]
weakLEq aLp (l,r) = extract aLp (\aLw w p -> do {
  addEQ (p,l);
  addLT (r,l);
  addEQ (r,w);
  pushAndCont weak aLw
})

weak :: M [()]
weak = do
  BranchState path <- get
  anyM [
    expand,
    -- S || \Gamma, s!~t
    case path of { NegAtom (PEq l r):_ -> addEQ (l,r) >> return []; _ -> throw },
    -- S || \Gamma L[p],\Delta,l~r
    case path of { (PosAtom (PEq l r):t) -> anyM [weakLEq aLp s | s <- [(l,r),(r,l)], aLp <- t]; _ -> throw },
    -- S || \Gamma l~r,\Delta,L[p]
    case path of { (aLp:t) -> anyM [weakLEq aLp (l,r) | PosAtom (PEq l r) <- t]; _ -> throw },
    -- S || \Gamma,!P[r],\Delta,P[s]
    -- S || \Gamma,P[r],\Delta,!P[s]
    case path of {
      NegAtom (PCustom n1 s):t -> anyM [mapM addEQ (zip r s) >> return [] | PosAtom (PCustom n2 r) <- t, n1 == n2];
      PosAtom (PCustom n1 s):t -> anyM [mapM addEQ (zip r s) >> return [] | NegAtom (PCustom n2 r) <- t, n1 == n2];
      NegAtom (PEq l r):t -> anyM [mapM addEQ (zip [l2,r2] s) | s <- [[l,r],[r,l]], PosAtom (PEq l2 r2) <- t];
      PosAtom (PEq l r):t -> anyM [mapM addEQ (zip [l2,r2] s) | s <- [[l,r],[r,l]], NegAtom (PEq l2 r2) <- t];
      _ -> throw
    }]

--------------------------------

convCla :: DNF.Cla -> [Atom]
convCla cla = (map PosAtom (SetM.toList $ DNF.pos cla)) ++ (map NegAtom (SetM.toList $  DNF.neg cla))

neg :: Atom -> Atom
neg (PosAtom p) = NegAtom p
neg (NegAtom p) = PosAtom p

prove :: DNF.Form -> Int -> IO (Maybe Int)
prove form nodesLimit = do
  let {
    -- negate the input form
    clauses = map (map neg . convCla) (SetM.toList $ DNF.cla form);
    initialState = TabState clauses 0 0 nodesLimit Set.empty Map.empty;
    -- start with expand step
    runBranch = StateM.runStateT expand (BranchState []);
    runTab = StateM.runStateT runBranch initialState;
    runExcept = ExceptM.runExcept runTab;
  }
  --print clauses 
  return $ case runExcept of
      Left () -> Nothing
      Right (_,s) -> Just (view varsUsed s)

proveLoop :: DNF.Form -> Int -> IO ()
proveLoop f limit = let
  rec f i = do
    res <- prove f i
    case res of {
      Nothing -> do {
        print i;
        if i<limit then rec f (i+1) else putStrLn "fail";
      };
      Just x -> putStrLn ("[" ++ show x ++ "]")
    }
  in rec f 0
