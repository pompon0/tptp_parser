module LibTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (testCase,assertFailure,assertBool,(@=?))

import Control.Lens (makeLenses, view, over)

import Lib

tests = testGroup "LibTest" [
  testCase "ix_view_test" $ ixViewTest,
  testCase "ix_view_oob_test" $ ixViewOobTest,
  testCase "ix_view_neg_test" $ ixViewNegTest,
  testCase "ix_over_test" $ ixOverTest,
  testCase "ix_over_oob_test" $ ixOverOobTest]

ixViewTest = view (ix 3) [5,4,3,16,4,3] @=? Just 16
ixViewOobTest = view (ix 10) [5,4,3,16,4,3] @=? Nothing
ixViewNegTest = view (ix (-3)) [5,4,3,16,4,3] @=? Nothing
ixOverTest = over (ix 3) (fmap (+2)) [0,1,2,3,4,5] @=? [0,1,2,5,4,5]
ixOverOobTest = over (ix 10) (fmap (+2)) [0,1,2,3,4,5] @=? [0,1,2,3,4,5]

