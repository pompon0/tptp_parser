module Build where

import Test.Tasty (testGroup)

import qualified ParserTest
import qualified LibTest

tests = testGroup "all" [
  --ParserTest.tests,
  LibTest.tests]
