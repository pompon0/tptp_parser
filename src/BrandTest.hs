module BrandTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion,testCaseSteps,testCase,assertFailure,assertBool,(@?=))

import Lib
import Pred
import DNF
import Brand
import qualified Trace
import qualified Parser
import ParserBin(toDNF)
import qualified TptpSampleData as P
import qualified Tableaux

tests = testGroup "BrandTest" [
  testCase "f = g" testEq,
  testCase "x = g" testVarFunEq]

eq a b = Atom True $ wrap $ PEq a b
neq a b = Atom False $ wrap $ PEq a b

f = wrap $ TFun 0 []
g = wrap $ TFun 1 []
x = wrap $ TVar 0
y = wrap $ TVar 1

oc = OrClause
occ = OrClauseCEE

-- This is a change-detector test,
-- refine the equivalence relation once needed.
testEq = do
  let got = cee $ NotAndForm [oc [eq f g]]
  -- refl axiom
  let { want = NotAndFormCEE [
    occ (oc [eq x x]) mempty [oc [eq x x]],
    occ (oc [eq f x, neq g x]) (oc [redLE f x, redLT g x]) [
      oc [eq f g],
      oc [eq f f],
      oc [eq f x, neq f g, neq f f, neq g x],
      oc [eq g g],
      oc [neq g g, neq g x, eq g x]],
    occ (oc [eq g x, neq f x]) (oc [redLE g x, redLT f x]) [
      oc [neq f g, eq g f],
      oc [eq f g],
      oc [eq g g],
      oc [eq g x, neq g f, neq g g, neq f x],
      oc [eq f f],
      oc [neq f f, neq f x, eq f x]]]
  }
  got @?= want

-- Test that second argument of equality gets expanded,
-- even if the first one is a variable
--
-- This is a change-detector test,
-- refine the equivalence relation once needed.
testVarFunEq = do
  let got = cee $ NotAndForm [oc [eq x g]]
  let { want = NotAndFormCEE [
    occ (oc [eq x x]) mempty [oc [eq x x]],
    occ (oc [eq x y, neq g y]) (oc [redLE x y, redLT g y]) [
      oc [eq x g],
      oc [eq x y, neq x g, neq g y],
      oc [eq g g],
      oc [neq g g, neq g y, eq g y]],
    occ (oc [eq g x]) (oc [redLE g x]) [
      oc [neq x g, eq g x],
      oc [eq x g],
      oc [eq g g],
      oc [eq g x, neq g x, neq g g, neq x x]]]
  }
  got @?= want
{-
      ,+eq(v0,v1) \/ -eq(f1(),v1)
      -p-3(v1,v0) \/ +p-3(f1(),v1)
        +eq(v0,f1())
        +eq(v0,v1) \/ -eq(v0,f1()) \/ -eq(f1(),v1)
        +eq(f1(),f1())
        -eq(f1(),f1()) \/ -eq(f1(),v1) \/ +eq(f1(),v1)
      ,+eq(f1(),v0)
      -p-3(v0,f1())
        -eq(v0,f1()) \/ +eq(f1(),v0)
        +eq(v0,f1())
        +eq(f1(),f1())
        +eq(f1(),v0) \/ -eq(f1(),v0) \/ -eq(f1(),f1()) \/ -eq(v0,v0)
      ]}
-}
