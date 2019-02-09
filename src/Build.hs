module Build where

import Test.Tasty (testGroup)

import qualified ParserTest
import qualified LibTest
import qualified SkolemTest
import qualified MGUTest
import qualified TableauxTest

tests = testGroup "all" [
  --ParserTest.tests,
  LibTest.tests,
  SkolemTest.tests,
  MGUTest.tests,
  TableauxTest.tests]
