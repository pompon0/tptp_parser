module LPO(lpo,Term(..)) where

--import Prelude hiding((<=))
import Skolem(Term(..))
--import qualified Prelude

{-
class POrd a where
  (<=) :: a -> a -> Bool

instance POrd Int where
  (<=) = (Prelude.<=)

instance POrd a => POrd [a] where
  [] <= _ = True
  (x:_) <= [] = False
  (x:xt) <= (y:yt) = x <= y && (not (y <= x) || xt <= yt)

instance (POrd a, POrd b) => POrd (a,b) where
  (xa,xb) <= (ya,yb) = xa <= ya && (not (ya <= xa) || xb <= yb)

-- s <= t
instance POrd Term where
  (TVar x) <= (TVar y) = x == y
  (TVar x) <= (TFun f args) = any (TVar x <=) args
  (TFun f args) <= (TVar x) = False
  s@(TFun sf sargs) <= t@(TFun tf targs) =
    any (t <=) sargs || (all (\a -> a <= s && a/=s) targs && (sf,sargs) <= (tf,targs))
-}

-- (prove transitivity)
--   induction on sum of term sizes
-- (prove subterm property)
--   induction
-- (by induction on term size prove irreflexivity)
--   We have x_j < f(x_i), so if x_j > f(x_i) then by transitivity x_j > x_j, which is false by induction.
--   Also inductively (x_i) /> (x_i)
-- (termination)
  -- out of infinite descending chains take lexicographically (by term size) smallest (which is not unique)
  -- some top level function will occur infinitely often, so take a subchain with it
  -- consider consecutive elements of the chain: f(u_1..u_n) > f(x_1..x_n)
  -- u_i /= f(x_1..x_n) and u_i /> f(x_1..x_n), since otherwise u_i could replace f(u_1..u_n) in the initial chain
  -- Therefore lexicographically (u_i) > (x_i). Since all args of all chain elements are well founded, the chain
  -- of words stabilizes, therefore so does the original chain
-- (totality on ground terms)
--   f(x_i) > y_j
--   g(y_i) > x_j
--   and inductively lexicographic order decides which is bigger

-- <=
lpo a b@(TVar x) = a == b
lpo a@(TVar x) (TFun f args) = any (lpo a) args
lpo a@(TFun af aa) b@(TFun bf ba) = let
  r False (ah:at) (bh:bt) = (lpo ah bh) && r (ah/=bh) at bt
  r False _ _ = True -- actually lists should be equal
  r True at _ = all (\x -> x/=b && lpo x b) at
  in any (lpo a) ba || (af<=bf && r (af/=bf) aa ba)

{-
lpo s t = (s==t) || case (s,t) of
  (_,TVar x) -> s /= t && mem x (fvt s)
  (TFun af aa,TFun bf bb) -> any (\x -> lpo x t) aa ||
    (all (\x -> s/=x && lpo s x) bb &&
    ((af == bf && lexord (/= && lpo) aa bb) || af>bf))
-}


  -- exists_i farg[i] >= t
  -- forall_i s >= gargs[i] && f:fargs >= g:gargs

  -- forall valuations
  -- exists_{x\in sub(s)} x >= t
  -- -exists_{x\in sub(t)} x >= s && f:fargs >= g:gargs
