module Build where

import Test.Tasty (testGroup)

import qualified ParserTest
import qualified LibTest
import qualified SkolemTest

tests = testGroup "all" [
  ParserTest.tests,
  LibTest.tests,
  SkolemTest.tests]
