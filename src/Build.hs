module Build where

import Test.Tasty (testGroup)

import qualified ParserTest

tests = testGroup "all" [ParserTest.tests]
