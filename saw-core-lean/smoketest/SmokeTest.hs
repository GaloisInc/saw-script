{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Direct-link regression tests for the Lean 4 backend. Each group
below targets a specific layer (pretty-printer, translator, goal
emission) so a failure's cause is obvious from the test name.
-}

module Main (main) where

import           Data.List           (isInfixOf)
import qualified Data.Text           as Text
import qualified Language.Lean.AST   as Lean
import qualified Language.Lean.Pretty as Lean
import           Prettyprinter        (Doc, defaultLayoutOptions, layoutPretty)
import           Prettyprinter.Render.String (renderString)

import           SAWCore.Prelude     (scLoadPreludeModule)
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor (mkSort)

import           SAWCoreLean.Lean

import           Test.Tasty          (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit    (assertBool, assertFailure, testCase)


defaultConfig :: TranslationConfiguration
defaultConfig = TranslationConfiguration
  { constantRenaming = []
  , constantSkips    = []
  }

render :: Doc ann -> String
render = renderString . layoutPretty defaultLayoutOptions

-- | Assert that @needle@ appears somewhere in @haystack@.
assertContains :: String -> String -> String -> IO ()
assertContains label needle haystack =
  assertBool (label ++ ": expected to contain " ++ show needle ++
              "\nin output:\n" ++ haystack)
             (needle `isInfixOf` haystack)

-- | Assert that @needle@ does /not/ appear anywhere in @haystack@.
assertNotContains :: String -> String -> String -> IO ()
assertNotContains label needle haystack =
  assertBool (label ++ ": expected to NOT contain " ++ show needle ++
              "\nin output:\n" ++ haystack)
             (not (needle `isInfixOf` haystack))

--------------------------------------------------------------------------------
-- Pretty-printer tests (pure AST; no SAWCore involved)
--------------------------------------------------------------------------------

prettyPrinterTests :: TestTree
prettyPrinterTests = testGroup "Language.Lean.Pretty"
  [ testCase "anonymous implicit pi prints as {_ : A} -> rest" $ do
      let d = Lean.Pi [Lean.PiBinder Lean.Implicit Nothing (Lean.Var "A")]
                     (Lean.Var "B")
          s = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "t" [] Nothing d))
      assertContains "anon implicit" "{_ : A}" s
      assertNotContains "anon implicit" "{A}" s

  , testCase "instance pi prints as [x : A] -> rest" $ do
      let d = Lean.Pi [Lean.PiBinder Lean.Instance (Just "inh") (Lean.Var "Inhabited")]
                     (Lean.Var "B")
          s = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "t" [] Nothing d))
      assertContains "instance pi" "[inh : Inhabited]" s

  , testCase "definition without binders or type has no double space" $ do
      let s = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "f" [] Nothing (Lean.Var "x")))
      assertNotContains "no double space" "f  " s
      assertContains    "def f :="        "def f :=" s

  , testCase "Let with no binders or type produces no double space" $ do
      let body = Lean.Let "x" [] Nothing (Lean.NatLit 7) (Lean.Var "x")
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "f" [] (Just (Lean.Var "Nat")) body))
      assertNotContains "no double space"   "x  " s
      assertContains    "let x := 7"        "let x := 7" s

  , testCase "If prints conventionally" $ do
      let body = Lean.If (Lean.Var "cond") (Lean.Var "t") (Lean.Var "f")
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "g" [] Nothing body))
      assertContains "if" "if cond then t else f" s

  , testCase "List prints with commas" $ do
      let body = Lean.List [Lean.NatLit 1, Lean.NatLit 2, Lean.NatLit 3]
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "xs" [] Nothing body))
      assertContains "list" "[1, 2, 3]" s

  , testCase "StringLit escapes double quotes and backslashes" $ do
      let body = Lean.StringLit "a\"b\\c"
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "msg" [] Nothing body))
      assertContains "string escape" "\"a\\\"b\\\\c\"" s

  , testCase "Tactic prints as by-block" $ do
      let body = Lean.Tactic "sorry"
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "t" [] (Just (Lean.Var "Prop")) body))
      assertContains "tactic" "by sorry" s

  , testCase "IntLit is parenthesized with Int ascription" $ do
      let body = Lean.IntLit (-7)
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "n" [] (Just (Lean.Var "Int")) body))
      assertContains "int lit" "(-7 : Int)" s

  , testCase "Ascription prints with a colon" $ do
      let body = Lean.Ascription (Lean.Var "x") (Lean.Var "Nat")
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "a" [] Nothing body))
      assertContains "ascription" "x : Nat" s

  , testCase "ExplVar prefixes with @" $ do
      let body = Lean.App (Lean.ExplVar "id") [Lean.Var "Bool", Lean.Var "true"]
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "a" [] Nothing body))
      assertContains "expl" "@id Bool true" s

  , testCase "Namespace wraps decls" $ do
      let inner = Lean.Definition Lean.Computable [] "bar" [] (Just (Lean.Var "Nat")) (Lean.NatLit 42)
          ns    = Lean.Namespace "Foo" [inner]
          s     = render (Lean.prettyDecl ns)
      assertContains "ns open" "namespace Foo" s
      assertContains "ns close" "end Foo" s
  ]

--------------------------------------------------------------------------------
-- Translator tests (require a SharedContext with the Prelude loaded)
--------------------------------------------------------------------------------

-- | Translate a SAWCore term and return the rendered output, or
-- throw an HUnit failure with the SAWCore-side error message.
translateOrFail :: SharedContext -> String -> Term -> IO String
translateOrFail sc label body = do
  bodyType <- scTypeOf sc body
  mm       <- scGetModuleMap sc
  case translateTermAsDeclImports defaultConfig mm (Lean.Ident label) body bodyType of
    Right doc -> pure (render doc)
    Left err -> do
      msg <- ppTranslationError sc err
      assertFailure (label ++ ": translation failed: " ++ Text.unpack msg)

translatorTests :: SharedContext -> TestTree
translatorTests sc = testGroup "SAWCoreLean.Term"
  [ testCase "\\(x : Bool) -> x" $ do
      boolTy <- scBoolType sc
      xName  <- scFreshVarName sc "x"
      xVar   <- scVariable   sc xName boolTy
      idBool <- scLambda     sc xName boolTy xVar
      s <- translateOrFail sc "identity" idBool
      assertContains "body" "def identity (x : Bool) : Bool" s
      -- The local binder should render as 'x' (the VarName's base
      -- name), not as a Prelude qualification.
      assertNotContains "no prelude qualifier for var"
                        "CryptolToLean.SAWCorePrelude.x" s

  , testCase "polymorphic \\(a : Type) (x : a) -> x emits no Inh_a binder" $ do
      typeSort <- scSort sc (mkSort 0)
      aName <- scFreshVarName sc "a"
      aVar  <- scVariable sc aName typeSort
      xName <- scFreshVarName sc "x"
      xVar  <- scVariable sc xName aVar
      innerLam <- scLambda sc xName aVar xVar
      outerLam <- scLambda sc aName typeSort innerLam
      s <- translateOrFail sc "polyId" outerLam
      -- The Stage-4.1 commit (c1f319ea5) removed the auto-injection
      -- of an @[Inh_a : Inhabited a]@ binder for parameters whose
      -- SAWCore type carries the @isort@ flag — it conflicted with
      -- SAWCore's positional recursor calls. This regression test
      -- pins that decision: ordinary type-polymorphic binders emit
      -- as bare @(a : Type)@ with no instance hypothesis attached.
      assertNotContains "no Inh_a binder injected" "Inh_a" s

  , testCase "Bool constant emits 'Bool', not qualified" $ do
      boolTy <- scBoolType sc
      s <- translateOrFail sc "boolTy" boolTy
      -- Body is rendered on a new line; just verify the bare short
      -- name appears and no Prelude qualifier sneaks in.
      assertContains "bare Bool" "Bool" s
      assertNotContains "not qualified" "CryptolToLean.SAWCorePrelude.Bool" s

    -- Note: an earlier version tested the 'UnderAppliedMacro' error
    -- path via Bit0 (a UseMacro 1 entry). Phase 2 landed removed
    -- those macro entries — the numeric-encoding collapse is handled
    -- by the generated SAWCorePrelude.lean instead. If/when a new
    -- UseMacro entry is added, this test slot is the right place to
    -- re-exercise the error path.
  ]

--------------------------------------------------------------------------------
-- Goal-emission tests
--------------------------------------------------------------------------------

goalEmissionTests :: SharedContext -> TestTree
goalEmissionTests sc = testGroup "SAWCoreLean.Lean.translateGoalAsDeclImports"
  [ testCase "emits theorem <name>_holds := by sorry" $ do
      -- Use any well-typed proposition. 'True' in SAWCore is a Bool
      -- constructor, not a Prop; easier to construct a closed Prop
      -- as @(x : Bool) -> Bool@ and pretend it's a goal for the sake
      -- of checking the shape of the theorem stub.
      boolTy  <- scBoolType sc
      xName   <- scFreshVarName sc "x"
      goalTy  <- scPi sc xName boolTy boolTy
      -- We don't have a real Prop here; just reuse the type for both
      -- term and type to exercise the printer path.
      mm      <- scGetModuleMap sc
      goalTp  <- scSort sc (mkSort 0)
      case translateGoalAsDeclImports defaultConfig mm (Lean.Ident "goal") goalTy goalTp of
        Left err -> do
          msg <- ppTranslationError sc err
          assertFailure ("goal translation failed: " ++ Text.unpack msg)
        Right doc -> do
          let s = render doc
          assertContains "goal def" "def goal" s
          assertContains "theorem stub" "theorem goal_holds : goal := by" s
          assertContains "sorry" "sorry" s
  ]

--------------------------------------------------------------------------------
-- Entry point
--------------------------------------------------------------------------------

main :: IO ()
main = do
  sc <- mkSharedContext
  scLoadPreludeModule sc
  defaultMain $ testGroup "saw-core-lean smoke tests"
    [ prettyPrinterTests
    , translatorTests sc
    , goalEmissionTests sc
    ]
