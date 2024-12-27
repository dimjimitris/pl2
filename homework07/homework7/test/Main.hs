module Main (main) where

import Test.Tasty
import Test.Tasty.QuickCheck
import MiniML
import Data.Proxy
import Gen

import Test.Tasty.Ingredients
import Test.Tasty.Options
import Test.Tasty.Runners

-- The main testing function. Runs a series of tests. Add as many additional
-- tests as you want.

ingredients :: [Ingredient]
ingredients = [consoleTestReporter, includingOptions [Option (Proxy :: Proxy QuickCheckTests)]]

main :: IO ()
main = defaultMainWithIngredients ingredients $ localOption (QuickCheckTests 100) $ testGroup "act"
  [ testProperty "Parser round trip" parserRoundTrip
  ,  testProperty "Typechecker" genTExpWellTyped
  , testProperty "Type soundness" typeSoundness
  ]

-- For any program in abstact syntax, pretty-printing it and parsing it
-- produces the original program (i.e., `parse . lex . showExp == id`)
parserRoundTrip :: Property
parserRoundTrip =
  forAll genExp (\e ->
    let txt = showExp e in
    case parse $ lexer txt of
      Left err -> whenFail (prettyErrs txt err) (counterexample "Parsing failed!" False)
      Right e' -> e === e')

-- TODO 3
-- 1. In the file Gen.hs add a generator that generates well typed programs. Aim to
--    cover as many language features as possible.
--
-- 2. Write a QuickCheck property to test that the typechecker produces the
--    expected type when given a random well-typed program of a specific type.
--    Use the generator implemented in step 1 to supply test cases.
--
-- 3. Write a QuickCheck property to verify the type soundness property of the
--    evaluation function. Specifically:
--
--    For every (terminating) well-typed program `e` of type `t`, the evaluation
--    function should terminate and produce a result configuration of type
--    `t`.
--
--    To test above property your well-typed program generator should generate
--    only terminating programs. In practice, it will be very unlikely for a
--    random generator to generate nonterminating programs. However, you may
--    tweak you generator to avoid generating truly recursive functions or limit
--    the recursion depth.
--
--    Note: In MiniML, references alone may introduce non-termination (see
--    examples/nonterm.ml), but it will be very hard to generate a random
--    program that does this, so you can ignore this case.


genTExpWellTyped :: Property
genTExpWellTyped = forAll genExpType $ \(e, t) ->
  case typeCheckTop e of
    Left err -> whenFail (prettyErrs (showExp e) err) (counterexample "Typechecking failed!" False)
    Right t' -> t === t'

typeSoundness :: Property
typeSoundness = forAll genExpType $ \(e, t) ->
  case evalTop e of
    Left err -> whenFail (prettyErrs (showExp e) err) (counterexample "Evaluation failed!" False)
    Right (v, s) -> case typeCheckVTop s v of
      Left err -> whenFail (prettyErrs (showExp e) err) (counterexample "Typechecking failed!" False)
      Right t' -> t === t'
