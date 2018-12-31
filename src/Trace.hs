{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Trace where

import Prelude hiding(fail,log)
import Control.Monad (liftM,ap)
import Test.Tasty.HUnit (assertBool,assertFailure,Assertion)
import Control.Monad.Trans.Class(lift)
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad.Trans.Except as Except
import qualified TraceM as N
import qualified System.Posix.Signals as Signals
import qualified Control.Concurrent.MVar as MVar

data Hash = Hash { channel :: MVar.MVar () }
type Stack = [String]
type Trace = State.StateT Hash (Except.ExceptT Stack IO)

checkChannel :: Trace ()
checkChannel = do
  h <- State.get
  s <- lift $ lift $ MVar.tryTakeMVar (channel h);
  case s of
    Just () -> N.fail "SIGINT"
    Nothing -> return ()

instance N.TraceM Trace where
  fail msg = lift $ Except.throwE [msg]
  ctx line args mx = do
    checkChannel
    State.mapStateT (Except.withExceptT
      (\s -> (line:map (\arg -> "  "++arg) args ++ s))) mx
  log msg = lift $ lift $ putStrLn msg

isOk :: Trace a -> IO Bool
isOk ta = do
  ioa <- evalIO ta
  return $ case ioa of
    Left _ -> False
    Right _ -> True

same :: (Eq a, Show a) => Trace a -> Trace a -> Trace ()
same mx my = do
  x <- mx
  y <- my
  if x==y then return () else N.fail (show x ++ " /= " ++ show y)

evalIO :: Trace a -> IO (Either Stack a)
evalIO ta = do
  chan <- MVar.newEmptyMVar
  let handler = do { MVar.tryPutMVar chan (); return (); }
  Signals.installHandler Signals.sigINT (Signals.Catch handler) Nothing
  Except.runExceptT (State.evalStateT ta (Hash chan))

-- TODO: do the printing
assertOk :: Trace a -> Assertion
assertOk ta = do
  mx <- evalIO ta
  case mx of
    Left s -> assertFailure (unlines s)
    Right _ -> return ()

assertNotOk :: Show a => Trace a -> Assertion
assertNotOk ta = do
  mx <- evalIO ta
  case mx of
    Left _ -> return ()
    Right a -> assertFailure ("expected error, got " ++ show a)
