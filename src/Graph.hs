{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types #-}

module Graph where

import Lib
import LibST
import Control.Lens(makeLenses,use,to,at,non,Lens',(&),(%~),(%=),(<%=),(^..),(^.),Getting)
import Control.Monad.ST
import Control.Monad(forM_)
import Data.STRef
import qualified Data.Map as Map

data Graph a = Graph { _vertices :: [a], _edges :: Map.Map a [a] }
makeLenses ''Graph

toGraph :: (Ord a, Eq a) => [(a,a)] -> Graph a 
toGraph e = Graph {
  _vertices = unique (map fst e ++ map snd e),
  _edges = foldl (\g (x,y) -> g & at x.non [] %~ (y:)) Map.empty e
}

--type State a = State { _deg :: Map a Int, _queue :: [a] }
at0 :: Ord a => a -> Lens' (Map.Map a Int) Int
at0 x = at x.non 0

cyclic :: Ord a => Graph a -> Bool
cyclic g = runST $ do
  deg <- newST Map.empty
  queue <- newST []
  forM_ (g^..edges.traverse.traverse) (\x -> deg *& at0 x %~ (+1))
  forM_ (g^.vertices) (\v -> whenM (deg*^.at0 v.to (==0)) (queue *& (v:)))
  loopM (pop queue) (\x -> do {
    forM_ (g^.edges.at x.non []) (\y -> do {
      deg *& at0 y %~ (+(-1));
      whenM (deg*^.at0 y.to (==0)) (queue *& (y:));
    });
  })
  readST deg >>= return.any (/=0)

