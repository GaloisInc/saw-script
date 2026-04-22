{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Text as Text
import qualified Language.Lean.AST as Lean
import Prettyprinter
import Prettyprinter.Render.String (renderString)

import SAWCore.Prelude (scLoadPreludeModule)
import SAWCore.SharedTerm
import SAWCore.Term.Functor (mkSort)

import SAWCoreLean.Lean

defaultConfig :: TranslationConfiguration
defaultConfig = TranslationConfiguration
  { constantRenaming = []
  , constantSkips = []
  }

render :: Doc ann -> String
render = renderString . layoutPretty defaultLayoutOptions

runTest :: SharedContext -> String -> Term -> IO ()
runTest sc label body = do
  bodyType <- scTypeOf sc body
  putStrLn ("=== " ++ label ++ " ===")
  case translateTermAsDeclImports defaultConfig (Lean.Ident label) body bodyType of
    Left err -> do
      msg <- ppTranslationError sc err
      putStrLn ("Error: " ++ Text.unpack msg)
    Right doc ->
      putStrLn (render doc)
  putStrLn ""

main :: IO ()
main = do
  sc <- mkSharedContext
  scLoadPreludeModule sc

  -- 1. Polymorphic identity at Type: \(x : Type 0) -> x
  typeSort <- scSort sc (mkSort 0)
  xName <- scFreshVarName sc "x"
  xVar <- scVariable sc xName typeSort
  idTypeLvl <- scLambda sc xName typeSort xVar
  runTest sc "idType" idTypeLvl

  -- 2. Two-argument constant function: \(a : Type 0) (b : Type 0) -> a
  aName <- scFreshVarName sc "a"
  aVar  <- scVariable sc aName typeSort
  bName <- scFreshVarName sc "b"
  bbody <- scLambda sc bName typeSort aVar
  constFun <- scLambda sc aName typeSort bbody
  runTest sc "constType" constFun

  -- 3. A pi type: (x : Type 0) -> Type 0 (a non-dependent arrow at Type)
  piTerm <- scPi sc xName typeSort typeSort
  runTest sc "idTypeTp" piTerm

  -- 4. Phase-0 flagship: \(x : Bool) -> x (exercises Constant path)
  boolTy <- scBoolType sc
  bName2 <- scFreshVarName sc "x"
  bVar   <- scVariable sc bName2 boolTy
  idBool <- scLambda sc bName2 boolTy bVar
  runTest sc "identity" idBool
