module MGUTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion,testCase,(@=?))

import Lib
import Pred
import qualified MGU
import qualified Data.Map as Map

tests = testGroup "MGUTest" [testCase "loop" loopTest]

loopTest = do
  let s0 = emptyValuation
  s1 <- assertMaybe $ MGU.runMGU (TVar $ VarName 1, TVar $ VarName 0) s0
  s2 <- assertMaybe $ MGU.runMGU (TVar $ VarName 0, TVar $ VarName 1) s1
  [(VarName 1,TVar $ VarName 0)] @=? Map.toList s2
