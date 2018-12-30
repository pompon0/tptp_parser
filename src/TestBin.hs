module TestBin where

import Test.Tasty (defaultMain,testGroup)
import Test.Tasty.HUnit (testCase)
import qualified Build

main = defaultMain $ Build.tests
