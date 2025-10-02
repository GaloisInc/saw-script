{- |
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Tests.Parser where

import Test.Tasty
import Test.Tasty.HUnit
import SAWCore.Module
import SAWCore.Name
import SAWCore.Prelude
import SAWCore.SharedTerm
import SAWCore.Term.Functor


namedMsg :: NameInfo -> String -> String
namedMsg sym msg = "In " ++ show (toAbsoluteName sym) ++ ": " ++ msg

checkDef :: Def -> Assertion
checkDef d = do
  let sym = nameInfo (defName d)
  let tp = defType d
  assertBool (namedMsg sym "Type is not ground.") (closedTerm tp)
  case defBody d of
    Nothing -> return ()
    Just body ->
      assertBool (namedMsg sym "Body is not ground.") (closedTerm body)

checkPrelude :: Assertion
checkPrelude =
  do sc <- mkSharedContext
     scLoadPreludeModule sc
     modmap <- scGetModuleMap sc
     mapM_ checkDef $ allModuleDefs modmap

parserTests :: [TestTree]
parserTests =
  [ testCase "preludeModule" checkPrelude
  ]
