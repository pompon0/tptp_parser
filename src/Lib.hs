module Lib where

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.List(intercalate)

getUnique :: Ord a => a -> Map.Map a Int -> (Int,Map.Map a Int)
getUnique k m = case Map.lookup k m of
  Just i -> (i,m)
  Nothing -> (Map.size m, Map.insert k (Map.size m) m)

splitBy :: Ord k => (a -> k) -> [a] -> Map.Map k [a]
splitBy f [] = Map.empty
splitBy f (h:t) = Map.alter (\ml -> Just (h:(Maybe.fromMaybe [] ml))) (f h) (splitBy f t)

ix :: Functor f => Int -> (Maybe a -> f (Maybe a)) -> ([a] -> f [a])
ix i g [] = fmap (\_ -> []) (g Nothing)
ix 0 g (h:t) = fmap (\ma -> case ma of { Nothing -> (h:t); Just x -> (x:t)}) (g (Just h))
ix i g (h:t) = fmap (\la -> h:la) (ix (i-1) g t)

sepList :: Show a => [a] -> String
sepList x = intercalate ", " (map show x)

assert :: Either String a -> IO a
assert (Left errMsg) = fail errMsg
assert (Right v) = return v

