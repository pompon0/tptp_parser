module GraphTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase,assertFailure,assertBool,(@?=))

import Graph

tests = testGroup "GraphTest" [
  testCase "path" $ cyclic (toGraph [(0,1),(1,2),(2,3)]) @?= False,
  testCase "cycle" $ cyclic (toGraph [(0,1),(1,2),(2,0)]) @?= True,
  testCase "cycleWithEdge" $ cyclic (toGraph [(0,4),(0,1),(1,2),(2,0)]) @?= True,
  testCase "tree" $ cyclic (toGraph [(1,5),(5,3),(5,4),(1,8),(1,10),(8,6)]) @?= False,
  testCase "dag" $ cyclic (toGraph [(7,5),(5,3),(3,4),(7,8),(8,4)]) @?= False,
  testCase "loop" $ cyclic (toGraph [(0,0)]) @?= True,
  testCase "empty" $ cyclic (toGraph [] :: Graph Int) @?= False]

