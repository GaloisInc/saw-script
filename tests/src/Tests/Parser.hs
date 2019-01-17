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
import Verifier.SAW.Module
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor


checkGroundTerm :: Term -> Bool
checkGroundTerm t = looseVars t == emptyBitSet

namedMsg :: Ident -> String -> String
namedMsg sym msg = "In " ++ show sym ++ ": " ++ msg

checkDef :: Def -> Assertion
checkDef d = do
  let sym = defIdent d
  let tp = defType d
  assertBool (namedMsg sym "Type is not ground.") (checkGroundTerm tp)
  case defBody d of
    Nothing -> return ()
    Just body ->
      assertBool (namedMsg sym "Body is not ground.") (checkGroundTerm body)

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
