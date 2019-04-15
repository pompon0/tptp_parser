{-# LANGUAGE ScopedTypeVariables #-}
module KBO(kbo) where

import Pred
import LibST
import Control.Monad.ST
import Data.STRef
import Data.Array.ST

{-
|s|_x = number of occurences of symbol x in term s

weight on symbols and total order on function symbols
  w : Fun\cup Var -> N
  \forall x\in Var. \mu = w(x)
  arity(c) = 0  =>  w(c) >= \mu
  w(f) = 0  =>  forall g\in Fun-{f}. f > g

KBO reduction order
s = f(s_i), t = g(t_i), x \in Var
s > t  <=>
  (\forall x\in Var. |s|_x >= |t|_x) && (
    w(s) > w(t) ||
    (w(s) = w(t) && f > g) ||
    (w(s) = w(t) && f = g && (s_i) > (t_i))
  )
s > x  <=> |s|_x > 0
-}

data State s = State {
  varBal :: STUArray s Int Int,
  posVarBalCount :: STRef s Int,
  negVarBalCount :: STRef s Int,
  weightBal :: STRef s Int
}

data Res = L | G | E | N deriving(Eq)

newSTUArray :: Ix i => (i,i) -> Int -> ST s (STUArray s i Int)
newSTUArray = newArray

-- O(|t|)
accum :: State s -> Int -> Term -> ST s ()
accum s dv t = case unwrap t of
  TVar x -> do
    weightBal s *& (+dv)
    xb <- readArray (varBal s) (fromIntegral x)
    let xb' = xb+dv
    writeArray (varBal s) (fromIntegral x) xb'
    posVarBalCount s *& (+(fromEnum (xb'>0) - fromEnum (xb>0)))
    negVarBalCount s *& (+(fromEnum (xb'<0) - fromEnum (xb<0)))
  TFun fn args -> do
    weightBal s *& (+dv)
    mapM_ (accum s dv) args

-- O(1); evaluates kbo comparison, assuming that var/weight balances have been
-- accumulatex and lex in the result of the lexicographic comparison of the arg lists
cmpAccum :: State s -> Res -> ST s Res
cmpAccum s lex = do
  pv <- readST (posVarBalCount s)
  nv <- readST (negVarBalCount s)
  w <- readST (weightBal s)
  return $ case (pv>0,nv>0) of
    (True,True) -> N
    (True,False) -> if w>0 || (w==0 && lex==G) then G else N
    (False,True) -> if w<0 || (w==0 && lex==L) then L else N
    (False,False) -> case compare w 0 of { LT -> L; GT -> G; EQ -> lex }

-- O(|t1|+|t2|); accumulates var/weight balances and evaluates kbo comparison
-- assumes that balances are initialized to 0
cmp :: State s -> (Term,Term) -> ST s Res
cmp s (t1,t2) = case (unwrap t1, unwrap t2) of
  (TFun fn fa, TFun gn ga) | t1/=t2 -> if fn/=gn then do
      mapM_ (accum s 1) fa
      mapM_ (accum s (-1)) ga
      cmpAccum s (case compare fn gn of { LT -> L; GT -> G; EQ -> E })
    else do
      let (h1:z1,h2:z2) = unzip (dropWhile (\(x,y) -> x==y) (zip fa ga))
      lex <- cmp s (h1,h2)
      mapM_ (accum s 1) z1
      mapM_ (accum s (-1)) z2
      cmpAccum s lex
  _ -> do 
    accum s 1 t1
    accum s (-1) t2
    if t1==t2 then return E else cmpAccum s N

-- O(varCount+|l|+|r|); performs kbo comparison assuming that all variables
-- are in [0.varCount)
kbo :: Int -> (Term,Term) -> Bool
kbo varCount (l,r) = runST $ do
  varBal <- newSTUArray (0,varCount-1) 0
  posVarBalCount <- newST 0
  negVarBalCount <- newST 0
  weightBal <- newST 0
  let s = State varBal posVarBalCount negVarBalCount weightBal
  res <- cmp s (l,r)
  return (res==L)

