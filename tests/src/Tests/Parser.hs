{- |
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Tests.Parser where

import Control.Applicative
import Control.Lens
import Control.Monad.Identity
import Data.Bits
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Verifier.SAW.Module
import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.Pretty

import Test.Tasty
import Test.Tasty.HUnit

checkGroundTerm :: Term -> Bool
checkGroundTerm t = looseVars t == emptyBitSet

namedMsg :: Ident -> String -> String
namedMsg sym msg = "In " ++ show sym ++ ": " ++ msg

checkDef :: Def -> Assertion
checkDef d = do
  let sym = defIdent d
  let tp = defType d
  let tpProp = assertBool (namedMsg sym "Type is not ground.") (checkGroundTerm tp)
  let bodyProps =
        case defBody d of
          Nothing -> []
          Just body ->
            assertBool (namedMsg sym "Body is not ground.") (checkGroundTerm body)

  sequence_ (tpProp : bodyProps)

checkPrelude :: Assertion
checkPrelude =
  do sc <- mkSharedContext
     scLoadPreludeModule sc
     modmap <- scGetModuleMap sc
     traverse_ checkDef $ allModuleDefs modmap

parserTests :: [TestTree]
parserTests =
  [ testCase "preludeModule" checkPrelude
  ]
