module LPO(lpo) where

import Pred

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
lpoE a b = case (unwrap a, unwrap b) of
  (_,TVar x) -> a == b
  (TVar x, TFun f args) -> any (lpoE a) args
  (TFun af aa, TFun bf ba) -> let
    r False (ah:at) (bh:bt) = (lpoE ah bh) && r (ah/=bh) at bt
    r False _ _ = True -- actually lists should be equal
    r True at _ = all (\x -> x/=b && lpoE x b) at
    in any (lpoE a) ba || (af<=bf && r (af/=bf) aa ba)

-- <
lpo a b = a/=b && lpoE a b

---------------------------------------------------------------

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

