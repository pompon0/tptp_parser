module TableauxTest(tests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (Assertion,testCaseSteps,testCase,assertFailure,assertBool,(@=?))

import Lib
import qualified Tableaux
import qualified Parser
import qualified Trace
import ParserBin(toDNF)

tests = testGroup "TableauxTest" [
  testCase "simple" $ runTest simple,
  testCase "barber" $ runTest barber,
  testCase "pelletier20" $ runTest pelletier20,
  testCase "pelletier24" $ runTest pelletier24]

runTest tptpString = do
  tptpFile <- Trace.evalIO (Parser.parse tptpString) >>= assert
  form <- assert $ toDNF tptpFile
  --putStrLn ("\n=== BEGIN FORM ===\n" ++ show form ++ "\n=== END FORM ===\n")
  proof <- Tableaux.proveLoop form 20 >>= assertMaybe >>= assertMaybe . Tableaux.toDNF
  print proof

simple = "fof(simple, conjecture, (?[X]:(![Y]: (p(X) => p(Y)))))."

barber = "fof(simple, conjecture, ~(?[B]:(![X]:(shaves(B,X) <=> ~shaves(X,X)))))."

pelletier20 = "\
\ fof(a1, axiom, (![X]: (![Y]: (?[Z]: (![W]: ((p(X) & q(Y)) => (r(Z) & u(W)))))))).\
\ fof(c, conjecture, (?[X]: (?[Y]: ((p(X) & q(Y)) => (?[Z]: r(Z))))))."

pelletier24 = "\
\ fof(a1, axiom, ~(?[X] : (u(X) & q(X)))).\
\ fof(a2, axiom, (![X] : (p(X) => (q(X) | r(X))))).\
\ fof(a3, axiom, ~(?[X] : (p(X) => (?[X]: q(X))))).\
\ fof(a4, axiom, (![X] : ((q(X) & r(X)) => u(X)))).\
\ fof(c, conjecture, (?[X] : (p(X) & r(X))))."
