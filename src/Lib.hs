{-# LANGUAGE ScopedTypeVariables #-}
module Lib where

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.List(intercalate)
import Data.List.Split(chunksOf)
import Control.Monad(join)

import System.IO(hFlush,stdout)
import qualified System.Posix.Signals as Signals
import qualified Control.Concurrent as Concurrent
import qualified Control.Concurrent.Thread.Delay as Delay
import qualified Control.Concurrent.Thread as Thread
import qualified Control.Concurrent.Timeout as Timeout

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
sepList x = intercalate "," (map show x)

assert :: Either String a -> IO a
assert (Left errMsg) = fail errMsg
assert (Right v) = return v

--------------------------------------

killable :: IO a -> IO a
killable cont = do
  ti <- Concurrent.myThreadId
  Signals.installHandler Signals.sigINT (Signals.Catch $ Concurrent.killThread ti) Nothing
  cont

-- capabilities count is the size of pthread pools
-- forkOS binds thread to a pthread
-- preemptive on memory allocation
--  if an infinite loop doesn't allocate memory it is not killable
--  SIGINT handler with cap=1 won't ever trigger
--  SIGINT handler with cap>1 will trigger, but will only schedule thread termination 
--  add flag "-fno-omit-yields" to enforce preemption
-- simplest tight loop (i.e. non-allocating)
--  loop :: Int -> Int
--  loop i = loop i

runInParallelWithTimeout :: Show a => Integer -> [IO a] -> IO [Thread.Result (Maybe a)]
runInParallelWithTimeout time_per_task_us tasks = do
  let {
    fork (i,t) = do {
      (_,w) <- Thread.forkOn i $ Timeout.timeout time_per_task_us t;
      return w;
    };
    execChunk :: Show a => [(Int,IO a)] -> IO [Thread.Result (Maybe a)];
    execChunk tasks = do {
      res <- mapM fork tasks >>= sequence;
      print $ zip (fst $ unzip tasks) res;
      putStrLn "section clear";
      hFlush stdout;
      return res;
    }
  }
  cap <- Concurrent.getNumCapabilities
  resChunks :: [[Thread.Result (Maybe a)]] <- mapM execChunk (chunksOf cap $ zip [0..] tasks)
  return (join resChunks)

