module DiscTreeTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion,testCaseSteps,testCase,assertFailure,assertBool,(@?=))

import Pred
import DiscTree
import Control.Lens((^..))
import qualified Data.Set as Set

tests = testGroup "DiscTreeTest" [
  testCase "q1" test1,
  testCase "q2" test2,
  testCase "q3" test3,
  testCase "q4" test4,
  testCase "q5" test5]

var vn = wrap (TVar vn)
fun fn args = wrap (TFun fn args)
f = fun 0
g = fun 1
a = fun 2
b = fun 3
c = fun 4
x = var 0
y = var 1

t1 = f[g[a[],x],c[]]
t2 = f[g[y,b[]],x]
t3 = f[g[a[],b[]],a[]]
t4 = f[g[x,c[]],b[]]
t5 = f[x,y]

tree = build [(t1,1),(t2,2),(t3,3),(t4,4),(t5,5)]
test1 = Set.fromList (tree^..match (f[g[a[],c[]],b[]])) @?= Set.fromList [4,5]
test2 = Set.fromList (tree^..match (f[g[a[],b[]],a[]])) @?= Set.fromList [2,3,5]
test3 = Set.fromList (tree^..match x) @?= Set.fromList [1,2,3,4,5]
test4 = Set.fromList (tree^..match (f[f[x,y],a[]])) @?= Set.fromList [5]
test5 = Set.fromList (tree^..match (f[g[a[],b[]],x])) @?= Set.fromList [1,2,3,5]
