{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module ShallowIndex where

import Pred
import qualified Data.Map as Map
import Control.Lens

data Swap s a = Swap [(s -> a, s)] a

swapId :: Swap s s -> Swap s s
swapId (Swap s i) = Swap ((id,i):s) i

instance Functor (Swap s) where
  fmap f (Swap s i) = Swap (s & traverse._1 %~ (f.)) (f i)

instance Applicative (Swap s) where
  pure x = Swap [] x
  Swap fs fi <*> Swap xs xi = Swap
    ((fs & traverse._1 %~ (\sf -> \s -> sf s xi)) ++ 
    (xs & traverse._1 %~ (\sx -> \s -> fi (sx s))))
    (fi xi)

swapAll :: Term -> Swap Term Term
swapAll t@(unwrap -> TVar _) = swapId (pure t)
swapAll (unwrap -> TFun fn args) = swapId $ pure (wrap.TFun fn) <*> traverse swapAll args

flatten :: Term -> Term
flatten (unwrap -> TFun fn args) = wrap (TFun fn [])
flatten (unwrap -> TVar _) = flatVar
flatVar = wrap (TVar 0)

type SubtermIndex q = Map.Map Term [(Term -> q,Term)]

emptySubtermIndex :: SubtermIndex q
emptySubtermIndex = Map.empty

build :: [Swap Term q] -> SubtermIndex q
build = foldr add emptySubtermIndex

add :: Swap Term q -> SubtermIndex q -> SubtermIndex q
add (Swap s _) index = foldl (\index x@(_,t) -> (index & at (flatten t :: Term).non' _Empty %~ (x:))) index s

lookup :: Term -> SubtermIndex q -> [(Term -> q, Term)]
lookup t index = let t' = flatten t in
  if t'==flatVar then index^..traverse.traverse 
  else index^.at t'.non' _Empty

