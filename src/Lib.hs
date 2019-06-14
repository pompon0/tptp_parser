{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lib where

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.List(intercalate)
import Data.List.Split(chunksOf)
import Control.Monad(join)

import Data.Monoid(Endo(..))
import Data.Functor.Const(Const(..))
import Data.Hashable(Hashable)
import Data.Ix(Ix)

import qualified Debug.Trace as Trace

import qualified Data.ProtoLens.TextFormat as TextFormat
import Data.ProtoLens.Message(Message)
import qualified Data.Text.Lazy as Text
import qualified Data.Set as Set

import Control.Monad.IO.Class(MonadIO,liftIO)
import System.IO(hFlush,hPutStrLn,stdout,stderr)
import qualified System.Posix.Signals as Signals
import qualified Control.Concurrent as Concurrent
import qualified Control.Concurrent.Thread.Delay as Delay
import qualified Control.Concurrent.Thread as Thread
import qualified Control.Concurrent.Timeout as Timeout

import qualified System.Clock as Clock

newtype FunName = FunName Int deriving (Eq,Num,Ord,Integral,Real,Enum,Hashable)
newtype PredName = PredName Int deriving(Eq,Num,Ord,Integral,Real,Enum,Hashable)
newtype VarName = VarName Int deriving (Eq,Num,Ord,Integral,Real,Enum,Hashable,Ix)

eqPredName = -1 :: PredName
redEQPredName = -2 :: PredName
redLTPredName = -3 :: PredName

extraConstName :: FunName
extraConstName = -1

instance Show FunName where {
  show fn | fn==extraConstName = "c" ;
  show (FunName n) = "f" ++ show n;
}
instance Show PredName where { show (PredName n) = "p" ++ show n }
instance Show VarName where { show (VarName n) = "v" ++ show n }

-------------------------------------------

dPrint :: (Monad m, Show a) => a -> m ()
dPrint = Trace.traceShowM 

compose :: [a -> a] -> (a -> a)
compose = foldl (.) id 

select :: [a] -> [([a],a,[a])]
select [] = []
select (h:t) = ([],h,t) : map (\(l,x,r) -> (h:l,x,r)) (select t)

unique :: Ord a => [a] -> [a]
unique = Set.toAscList . Set.fromList

getUnique :: (Ord a, Num b) => a -> Map.Map a b -> (b,Map.Map a b)
getUnique k m = case Map.lookup k m of
  Just i -> (i,m)
  Nothing -> let i = fromIntegral (Map.size m) in (i, Map.insert k i m)

splitBy :: Ord k => (a -> k) -> [a] -> Map.Map k [a]
splitBy f [] = Map.empty
splitBy f (h:t) = Map.alter (\ml -> Just (h:(Maybe.fromMaybe [] ml))) (f h) (splitBy f t)

ix :: (Functor f, Num b, Ix b) => b -> (Maybe a -> f (Maybe a)) -> ([a] -> f [a])
ix i g [] = fmap (\_ -> []) (g Nothing)
ix 0 g (h:t) = fmap (\ma -> case ma of { Nothing -> (h:t); Just x -> (x:t)}) (g (Just h))
ix i g (h:t) = fmap (\la -> h:la) (ix (i-1) g t)

sepList :: Show a => [a] -> String
sepList x = intercalate "," (map show x)

assert :: (Monad m, Show e) => Either e a -> m a
assert (Left err) = fail (show err)
assert (Right v) = return v

assertMaybe :: Monad m => Maybe a -> m a
assertMaybe Nothing = fail "Nothing"
assertMaybe (Just v) = return v

orFail :: Monad m => String -> Maybe a -> m a
orFail msg Nothing = fail msg
orFail _ (Just v) = return v

--------------------------------------

putStrLnE :: MonadIO m => String -> m ()
putStrLnE s = liftIO (hPutStrLn stderr s >> hFlush stderr)
printE :: (MonadIO m, Show a) => a -> m ()
printE x = putStrLnE (show x)

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

runInParallelWithTimeout :: Show a => Integer -> [(String,IO a)] -> IO [Thread.Result (Maybe a)]
runInParallelWithTimeout time_per_task_us tasks = do
  let {
    fork (i,(n,t)) = do {
      (_,w) <- Thread.forkOn i $ Timeout.timeout time_per_task_us t;
      return $ do { r <- w; putStrLn $ n ++ " = " ++ show r; hFlush stdout; return r };
    };
    execChunk :: Show a => [(Int,(String,IO a))] -> IO [Thread.Result (Maybe a)];
    execChunk tasks = mapM fork tasks >>= sequence;
  }
  cap <- Concurrent.getNumCapabilities
  resChunks :: [[Thread.Result (Maybe a)]] <- mapM execChunk (chunksOf cap $ zip [0..] tasks)
  return (join resChunks)

--------------------------------------------

readProtoFile :: Message a => String -> IO a
readProtoFile path = readFile path >>= assert . TextFormat.readMessage . Text.pack 

--------------------------------------------
{-
type Getting r s t a b = (a -> Const r b) -> (s -> Const r t)
toListOf :: Getting [a] s t a b -> s -> [a]
toListOf t = getConst . t (\a -> Const [a])

(^..) :: s -> Getting [a] s t a b -> [a]
(^..) = flip toListOf

(^.) :: s -> Getting a s t a b -> a
(^.) s g = getConst $ g (\a -> Const a) s
infix 8 ^.,^..
-}
--------------------------------------------

diffSeconds :: Clock.TimeSpec -> Clock.TimeSpec -> Double
diffSeconds t1 t0 = (*1e-9) $ fromIntegral $ Clock.toNanoSecs $ Clock.diffTimeSpec t1 t0

