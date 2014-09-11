{-# LANGUAGE DoAndIfThenElse #-}

{- |
Copyright   : Galois, Inc. 2012-2014
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
import Data.Proxy

import System.Exit

import Tests.BitBlast
import Tests.Parser
import Tests.SharedTerm
import Tests.Rewriter

main :: IO ()
main = defaultMainWithIngredients ingrs tests

ingrs :: [Ingredient]
ingrs =
   [ antXMLRunner
   ]
   ++
   defaultIngredients

tests :: TestTree
tests =
   testGroup "SAWCore"
   [ testGroup "SharedTerm" sharedTermTests
   , testGroup "Parser" parserTests
   , testGroup "BitBlast" bitblastTests
   , testGroup "Rewriter" rewriter_tests
   ]
