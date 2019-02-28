module SkolemTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (assertFailure,testCase,assertBool,(@?=))

import qualified NNF as N
import qualified Skolem as S
import qualified Pred as P

tests = testGroup "SkolemTest" [
  testCase "simpleForall" testSimpleForall,
  testCase "simpleExists" testSimpleExists,
  testCase "FE" testFE,
  testCase "EF" testEF]

testSimpleForall = do
  let refl = N.PEq (N.TVar 0) (N.TVar 0)
  let nnf = N.Forall $ N.PosAtom $ refl
  S.skol nnf @?= (S.PosAtom $ P.PEq (P.TFun 0 []) (P.TFun 0 []))

testSimpleExists = do
  let refl = N.PEq (N.TVar 0) (N.TVar 0)
  let nnf = N.Exists $ N.PosAtom $ refl
  S.skol nnf @?= (S.PosAtom $ P.PEq (P.TVar 0) (P.TVar 0))

testFE = do
  let refl = N.PEq (N.TVar 0) (N.TVar 1)
  let nnf = N.Forall $ N.Exists $ N.PosAtom $ refl
  S.skol nnf @?= (S.PosAtom $ P.PEq (P.TVar 0) (P.TFun 0 []))

testEF = do
  let refl = N.PEq (N.TVar 1) (N.TVar 0)
  let nnf = N.Exists $ N.Forall $ N.PosAtom $ refl
  S.skol nnf @?= (S.PosAtom $ P.PEq (P.TVar 0) (P.TFun 0 [P.TVar 0]))


