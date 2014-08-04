{- |
Copyright   : Galois, Inc. 2012-2014
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
import Text.PrettyPrint.Leijen hiding ((<$>))

import Tests.Common

import Verifier.SAW.Prelude
import Verifier.SAW.TypedAST


checkGroundTerm :: Term -> Bool
checkGroundTerm t = freesTerm t == 0

namedMsg :: Ident -> String -> String
namedMsg sym msg = "In " ++ show sym ++ ": " ++ msg


failWith :: Ident -> String -> Gen a
failWith sym msg = fail (namedMsg sym msg)

checkEqn :: Ident -> TypedDefEqn -> Property
checkEqn sym (DefEqn pats rhs@(Term rtf)) = do
  let nbound = sum $ patBoundVarCount <$> pats
  let lvd = emptyLocalVarDoc
          & docShowLocalNames .~ False
          & docShowLocalTypes .~ True
  let msg = "Equation right hand side has unbound variables:\n"
         ++ show (ppDefEqn ppTerm emptyLocalVarDoc (ppIdent sym) (DefEqn pats rhs)) ++ "\n"
         ++ show (ppTerm lvd PrecNone rhs) ++ "\n"
         ++ show (freesTerm rhs) ++ "\n"
         ++ show (ppTermF (\_ _ -> text . show) lvd PrecNone (freesTerm <$> rtf))

  printTestCase
    (namedMsg sym msg)
    (freesTerm rhs `shiftR` nbound == 0)

checkDef :: TypedDef -> Property
checkDef d = do
  let sym = defIdent d
  let tp = defType d
  let tpProp = printTestCase (namedMsg sym "Type is not ground.")
                             (checkGroundTerm tp)
  let eqProps = checkEqn sym <$> defEqs d
  conjoin (tpProp : eqProps)

checkModule :: Module -> Property
checkModule m = conjoin $ checkDef <$> moduleDefs m

parserTests :: [TestCase]
parserTests =
  [ mkTestCase "preludeModule" $ checkModule preludeModule
  ]