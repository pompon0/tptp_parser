module Build where

import Test.Tasty (testGroup)

import qualified ParserTest
import qualified LibTest
import qualified SkolemTest
import qualified MGUTest
import qualified TableauxTest
import qualified LazyParamTest
import qualified DiscTreeTest
import qualified GraphTest
import qualified KBOTest
import qualified BrandTest

tests = testGroup "all" [
  ParserTest.tests,
  LibTest.tests,
  SkolemTest.tests,
  MGUTest.tests,
  TableauxTest.tests,
  LazyParamTest.tests,
  DiscTreeTest.tests,
  GraphTest.tests,
  KBOTest.tests,
  BrandTest.tests]
