{-# LANGUAGE DoAndIfThenElse #-}

{- |
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Main where

import Test.Tasty
import Test.Tasty.Options
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML
import Test.Tasty.QuickCheck
import Data.Proxy

import Tests.CacheTests
import Tests.Parser
import Tests.SharedTerm
import Tests.Rewriter

main :: IO ()
main = defaultMainWithIngredients ingrs tests

ingrs :: [Ingredient]
ingrs =
   [ antXMLRunner
   -- explicitly including this option keeps the test suite from failing due
   -- to passing the '--quickcheck-tests' option on the command line
   , includingOptions [ Option (Proxy :: Proxy QuickCheckTests) ]
   ]
   ++
   defaultIngredients

tests :: TestTree
tests =
   testGroup "SAWCore"
   [ testGroup "SharedTerm" sharedTermTests
   , testGroup "Parser" parserTests
   , testGroup "Rewriter" rewriter_tests
   , testGroup "Cache" cacheTests
   ]
