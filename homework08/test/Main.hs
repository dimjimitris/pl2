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
main = defaultMainWithIngredients ingredients $ localOption (QuickCheckTests 10000) $ testGroup "act"
  [ testProperty "Parser round trip" parserRoundTrip, 
    testProperty "Type inference" testTypeInf ]

-- A property that for a randomly MiniML as pretty-printing it and parsing it
-- produces the original program (i.e., `parse . lex . showExp == id`)
parserRoundTrip :: Property
parserRoundTrip =
  forAll genExp (\e ->
    let txt = showExp e in
    case parse $ lexer txt of
      Left err -> whenFail (prettyErrs txt err) (counterexample "Parsing failed!" False)
      Right e' -> e === e')


testTypeInf :: Property
testTypeInf = forAll genExpType $ \(e, t) ->
  case inferTypeTop e of
    Left err -> whenFail (prettyErrs (showExp e) err) (counterexample "Type inference failed!" False)
    Right t' -> case unify [(t, fromScheme t', nowhere)] of
                  Left err -> whenFail (prettyErrs (showExp e) err) (counterexample "Unification failed!" False)
                  Right _  -> property True
  where
    fromScheme :: TypeScheme -> Type
    fromScheme (Type t) = t
    fromScheme (Forall _ t) = t
