module KBOTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase,assertFailure,assertBool,(@?=))

import Pred
import KBO

var vn = wrap $ TVar (fromIntegral vn)
fun fn args = wrap $ TFun (fromIntegral fn) args

x = var 0
y = var 1
f = fun 0
g = fun 1
h = fun 2

tests = testGroup "KBOTest" [
  testCase "x<x" $ kbo 10 (x,x) @?= False,
  testCase "x<f(x)" $ kbo 10 (x,f[x]) @?= True,
  testCase "f(x)<x" $ kbo 10 (f[x],x) @?= False,
  testCase "x<f(y)" $ kbo 10 (x,f[y]) @?= False,
  testCase "x<f(y,x)" $ kbo 10 (x,f[y,x]) @?= True,
  testCase "g(x)<f(y,g(x))" $ kbo 10 (g[x],f[y,g[x]]) @?= True,
  testCase "g(g(y))<f(y,g(x))" $ kbo 10 (g[g[y]],f[y,g[x]]) @?= True,
  testCase "g(g(g(g(y))))<f(y,g(x))" $ kbo 10 (g[g[g[g[y]]]],f[y,g[x]]) @?= False,
  testCase "f(y,g(x))<g(g(g(g(y))))" $ kbo 10 (f[y,g[x]],g[g[g[g[y]]]]) @?= False,
  testCase "f(y,g(x))<f(y,h(x))" $ kbo 10 (f[y,g[x]],f[y,h[x]]) @?= True]

