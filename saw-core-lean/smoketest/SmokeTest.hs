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
import           SAWCore.Term.Functor (mkSort, propSort)

import           SAWCentral.Prover.Exporter
                  ( discoverNatRecReachers
                  , iterateNormalizeToFixedPoint
                  , polymorphismResidual
                  , scNormalizeForLeanMaxIters )

import           SAWCoreLean.Lean
import           SAWCoreLean.SpecialTreatment (escapeIdent)

import           Control.Exception   (try, SomeException, evaluate)
import qualified Data.Set            as Set

import           Test.Tasty          (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit    (assertBool, assertFailure, testCase, (@?=))


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

  , testCase "ArrayValue renders as Lean Vector literal #v[...]" $ do
      -- SAWCore array literals translate to a 'Lean.List' on the
      -- AST side; the pretty-printer renders them as Lean's typed-
      -- vector literal '#v[...]'. Pin this — emitting plain '[...]'
      -- (Lean 'List' literal) would type-mismatch every emitted
      -- Vec value. Regression test for Arc 1.7 / Stage-2 Vec
      -- elaboration.
      boolTy   <- scBoolType sc
      true     <- scBool sc True
      false    <- scBool sc False
      arrayTm  <- scVector sc boolTy [true, false]
      s <- translateOrFail sc "litVec" arrayTm
      assertContains "vec literal" "#v[" s
      assertNotContains "no list literal at the head" "= [" s

  , testCase "empty ArrayValue renders as #v[] not []" $ do
      -- Same regression but for the empty case, which is the
      -- specific shape that broke in test_literals.t1 ('Vec 0 _').
      boolTy   <- scBoolType sc
      arrayTm  <- scVector sc boolTy []
      s <- translateOrFail sc "emptyVec" arrayTm
      assertContains "empty vec literal" "#v[]" s

  , testCase "applied constructor emits @-prefix at use site (L-9)" $ do
      -- L-9 lockdown. SAWCore applies constructor parameters
      -- explicitly; Lean's auto-generated ctors take them as
      -- implicits. Emit a leading `@` (Lean.ExplVar) to keep the
      -- positional argument list intact. A regression that drops
      -- the prefix would silently mis-apply implicit-vs-explicit
      -- args at every translated constructor — caught here.
      --
      -- 'Either.Left' is in our SpecialTreatment under
      -- 'mapsToExpl' so the @ comes from the (expl=True) branch
      -- in Term.hs translateIdentWithArgs.apply. Any CTor whose
      -- treatment defaults to UsePreserve goes through the
      -- isCtor branch in the same function — that branch is
      -- exercised every time a SAWCore datatype's constructor
      -- without an explicit mapping is encountered (rare in
      -- practice given our table coverage, but the check fires
      -- the same Lean.ExplVar.)
      natTy <- scNatType sc
      zero  <- scNat sc 0
      left  <- scGlobalApply sc "Prelude.Left" [natTy, natTy, zero]
      s <- translateOrFail sc "leftZero" left
      assertContains "@-prefix on Left ctor" "@Either.Left" s

    -- L-9's other half — recursor heads emit '@<DT>.rec' — is
    -- pinned indirectly by every integration test under
    -- 'otherTests/saw-core-lean/' whose '.lean.good' contains a
    -- recursor (e.g. 'test_cryptol_module_simple.module.lean.good'
    -- has '@Bool.rec', '@Num.rec', '@RecordType.rec', etc.). The
    -- corresponding code path in Term.hs:609 emits
    -- 'Lean.ExplVar (Lean.Ident (i ++ ".rec"))', i.e. forces the
    -- '@' prefix exactly the same way 'apply isCtor' does. A
    -- regression that drops that ExplVar would show up as a diff
    -- against every one of those .lean.good files.

  , testCase "scNormalize cap fails loud, never silent (L-6)" $ do
      -- L-6 lockdown. The 100-iter cap in scNormalizeForLean is a
      -- safety net for runaway normalization (translator bugs,
      -- genuinely-recursive defs). The lockdown bar: when the cap
      -- fires, it MUST throw — never silently return a partially-
      -- normalized term.
      --
      -- 'iterateNormalizeToFixedPoint' is the cap-loop refactored
      -- out of scNormalizeForLean. We pass a mock normaliser that
      -- never converges (returns a fresh term each call) and verify
      -- that:
      --   1. The function throws (we don't get a result back).
      --   2. The thrown message names the cap and the iteration
      --      count, so a future user hitting it has actionable
      --      diagnostics.
      --
      -- We use a small cap (5) to keep the test fast.
      true  <- scBool sc True
      false <- scBool sc False
      let mockNormalize :: Term -> IO Term
          mockNormalize t =
            -- Always return the OTHER bool than the input. SAWCore's
            -- hash-cons gives stable termIndex per term, so the loop
            -- never sees equality.
            pure $ if termIndex t == termIndex true then false else true
      result <- try (iterateNormalizeToFixedPoint 5 mockNormalize true
                       >>= evaluate)
                :: IO (Either SomeException Term)
      case result of
        Left e -> do
          let msg = show e
          assertContains "names cap behavior"
                         "exceeded 5 iterations" msg
          assertContains "names the function"
                         "scNormalizeForLean" msg
        Right _ ->
          assertFailure
            "iterateNormalizeToFixedPoint returned normally with a \
            \never-converging normaliser; cap should have thrown"

  , testCase "escapeIdent: ordinary alphanumeric names pass through (L-11)" $ do
      -- L-11 lockdown. The escape policy: Cryptol-style alphanumeric
      -- identifiers (with _ and ') stay unchanged; anything else
      -- gets Z-encoded with an Op_ prefix. New under L-11: Lean
      -- reserved words ALSO get Z-encoded, even though they look
      -- alphanumeric — to prevent a SAW name like 'match' or 'do'
      -- shadowing Lean syntax at the def site.
      escapeIdent (Lean.Ident "foo")        @?= Lean.Ident "foo"
      escapeIdent (Lean.Ident "fooBar")     @?= Lean.Ident "fooBar"
      escapeIdent (Lean.Ident "foo_bar")    @?= Lean.Ident "foo_bar"
      escapeIdent (Lean.Ident "foo'")       @?= Lean.Ident "foo'"
      escapeIdent (Lean.Ident "x42")        @?= Lean.Ident "x42"

  , testCase "escapeIdent: special chars trigger Z-encoding (L-11)" $ do
      -- Anything outside [A-Za-z0-9_'] forces the Op_<zenc> path.
      let isOpEncoded (Lean.Ident s) = "Op_" `isInfixOf` s
      assertBool "exclamation"
                 (isOpEncoded (escapeIdent (Lean.Ident "foo!")))
      assertBool "dollar"
                 (isOpEncoded (escapeIdent (Lean.Ident "foo$bar")))
      assertBool "operator-style"
                 (isOpEncoded (escapeIdent (Lean.Ident "<*>")))
      -- '\955' (λ) is a Unicode LETTER and isAlphaNum-true; that's
      -- legal SAW syntax and SHOULD pass through. Use a clearly
      -- non-letter symbol instead.
      assertBool "arrow symbol"
                 (isOpEncoded (escapeIdent (Lean.Ident "foo→bar")))

  , testCase "escapeIdent: Lean reserved words get escaped (L-11)" $ do
      -- The "looks fine but isn't" set. Without this, a SAW name
      -- like 'match' would emit 'def match := ...' and fail Lean
      -- parsing. Spot-check several common collisions.
      let isOpEncoded (Lean.Ident s) = "Op_" `isInfixOf` s
      assertBool "match keyword"
                 (isOpEncoded (escapeIdent (Lean.Ident "match")))
      assertBool "do keyword"
                 (isOpEncoded (escapeIdent (Lean.Ident "do")))
      assertBool "for keyword"
                 (isOpEncoded (escapeIdent (Lean.Ident "for")))
      assertBool "where keyword"
                 (isOpEncoded (escapeIdent (Lean.Ident "where")))
      assertBool "instance keyword"
                 (isOpEncoded (escapeIdent (Lean.Ident "instance")))
      assertBool "Type keyword"
                 (isOpEncoded (escapeIdent (Lean.Ident "Type")))
      assertBool "Prop keyword"
                 (isOpEncoded (escapeIdent (Lean.Ident "Prop")))

  , testCase "escapeIdent: distinct inputs produce distinct outputs (L-11)" $ do
      -- Z-encoding is injective; the Op_ prefix preserves that.
      -- Pin a few likely collision shapes.
      let outs = map (\(Lean.Ident s) -> s)
                   [ escapeIdent (Lean.Ident "match")
                   , escapeIdent (Lean.Ident "Match")
                   , escapeIdent (Lean.Ident "match_")
                   , escapeIdent (Lean.Ident "match!")
                   , escapeIdent (Lean.Ident "Op_match")
                   ]
      assertBool "outputs distinct"
                 (length outs == length (foldr (\x ys ->
                    if x `elem` ys then ys else x:ys) [] outs))

  , testCase "discoverNatRecReachers covers all 5 unsound recursor types (L-3)" $ do
      -- L-3 lockdown. Pre-L-3, only Nat#rec / Pos#rec usages were
      -- auto-detected; Z#rec / AccessibleNat#rec / AccessiblePos#rec
      -- were covered only by the textual leanOpaqueBuiltins list.
      -- Now all five datatypes are checked by the auto-derive,
      -- making the textual list a convenience (for surface
      -- cleanliness) rather than a soundness backstop.
      --
      -- This test pins one representative def per recursor type:
      reachers <- discoverNatRecReachers sc
      let probe nm = do
            idxs <- scResolveName sc nm
            case idxs of
              []    -> assertFailure
                         ("could not resolve " ++ Text.unpack nm)
              (i:_) ->
                assertBool
                  (Text.unpack nm ++
                   " not auto-derived as Nat-rec-reacher")
                  (i `Set.member` reachers)
      -- Nat#rec: Succ uses Nat#rec directly via NatPos chain.
      probe "Succ"
      -- Pos#rec: Pos_cases is `Pos#rec (\_ -> a)`.
      probe "Pos_cases"
      -- Z#rec: Z_cases is `Z#rec (\_ -> a)`.
      probe "Z_cases"
      -- AccessiblePos#rec: AccessiblePos_Bit0 uses it directly.
      probe "AccessiblePos_Bit0"
      -- AccessibleNat#rec / #rec1: Nat__rec uses AccessibleNat#rec1.
      probe "Nat__rec"

  , testCase "translateSort: SAW sort 0 collapses to Lean Type (L-10)" $ do
      -- L-10 lockdown. translateSort is the single point of trust
      -- in our universe handling: it collapses every non-Prop SAW
      -- sort to Lean's Type. We never produce Type 1 / Type 2 etc.
      -- on the Lean side, even when SAW emitted a higher sort.
      --
      -- The L-1 polymorphismResidual gate rejects Pi BINDERS at
      -- sort k>0, so the only sort that can land in translator-
      -- emitted output is sort 0 — and it collapses to 'Type'.
      -- This test pins that collapse: a SAW term that IS sort 0
      -- (i.e. the 'Type 0' universe expression) renders as 'Type'
      -- in Lean.
      sort0 <- scSort sc (mkSort 0)
      s <- translateOrFail sc "ty" sort0
      assertContains "sort 0 → Type" "Type" s
      -- Specifically: we don't drift to a numeric universe.
      assertNotContains "no Type 1 leak" "Type 1" s
      assertNotContains "no Sort drift" "Sort " s

  , testCase "translateSort: SAW Prop stays as Lean Prop (L-10)" $ do
      -- The other half of the contract. SAW's propSort is Lean's
      -- Prop; no collapse, no universe drift. The translator's
      -- Prop is load-bearing for goal emission — every offline_lean
      -- output is a Prop-typed def. Output here is roughly:
      --   noncomputable def tyP : Type := Prop
      -- where the body is the Lean term `Prop` (= Sort 0). The
      -- type annotation itself is `: Type` because the universe
      -- of Prop in Lean is Type.
      sortP <- scSort sc propSort
      s <- translateOrFail sc "tyP" sortP
      -- Match the def-body line. Prettyprinter wraps after ':=' so
      -- the body sits on a fresh indented line.
      assertContains "Prop appears as def body" "Prop" s
      -- Sanity: no untranslated 'Sort' AST leak.
      assertNotContains "no Sort drift" "Sort " s

  , testCase "polymorphismResidual catches outer sort 1 binder (L-1)" $ do
      -- Direct smoketest of the residual-detection function. Pairs
      -- with the intTest-level coverage in
      -- test_lean_soundness_polymorphic / _nested. Sub-second; runs
      -- on every cabal test push without needing a saw binary.
      typeSort <- scSort sc (mkSort 1)
      aName    <- scFreshVarName sc "a"
      aVar     <- scVariable sc aName typeSort
      tp       <- scPi sc aName typeSort aVar
      -- tp is roughly: (a : sort 1) -> a — binds a sort-1 variable
      -- on the outer pi-spine. Must be flagged.
      mResidual <- polymorphismResidual tp
      case mResidual of
        Just msg ->
          assertContains "names the offending binder" "sort 1" msg
        Nothing ->
          assertFailure "polymorphismResidual missed an outer sort 1 binder"

  , testCase "polymorphismResidual catches NESTED sort 1 binder (L-1)" $ do
      -- The L-1 lockdown specifically: nested binders must also be
      -- caught. asPiList-only walks would miss this. tp here is:
      --   ((a : sort 1) -> a) -> Bool
      -- The sort 1 binder is inside the argument type of the outer
      -- f binder. The full term-tree walk added in L-1 must catch
      -- it at the same site.
      typeSort <- scSort sc (mkSort 1)
      boolTy   <- scBoolType sc
      aName    <- scFreshVarName sc "a"
      aVar     <- scVariable sc aName typeSort
      innerPi  <- scPi sc aName typeSort aVar
      fName    <- scFreshVarName sc "f"
      tp       <- scPi sc fName innerPi boolTy
      mResidual <- polymorphismResidual tp
      case mResidual of
        Just msg ->
          assertContains "names the nested binder" "a : sort 1" msg
        Nothing ->
          assertFailure
            "polymorphismResidual missed a nested sort 1 binder"

  , testCase "polymorphismResidual passes Type 0 polymorphism (L-1)" $ do
      -- Negative: a sort 0 binder (Cryptol's '{a}' over types) is
      -- NOT a residual — translation handles Type 0 polymorphism
      -- fine. Confirm we don't false-positive.
      typeSort <- scSort sc (mkSort 0)
      aName    <- scFreshVarName sc "a"
      aVar     <- scVariable sc aName typeSort
      tp       <- scPi sc aName typeSort aVar
      mResidual <- polymorphismResidual tp
      case mResidual of
        Just msg ->
          assertFailure $
            "polymorphismResidual false-positived on a Type 0 binder: "
            ++ msg
        Nothing -> pure ()

  , testCase "scNormalize cap is set to 100 iterations (L-6 doc pin)" $ do
      -- Pin the documented cap value. If somebody bumps it (or
      -- drops it), this test forces them to update both the
      -- constant and the soundness doc that cites it. Cheap
      -- documentation-vs-code consistency check.
      assertBool "max iters constant is 100"
                 (scNormalizeForLeanMaxIters == 100)

  , testCase "SAW ite/iteDep argument order preserved (L-7)" $ do
      -- L-7 lockdown. SAWCore's Bool data is `data Bool { True;
      -- False; }` — True first. Lean's `Bool.rec` is the
      -- opposite. Translation routes SAWCore `ite` and `iteDep`
      -- through hand-written wrappers in SAWCorePreludeExtra
      -- (defined as `Bool.rec falseCase trueCase scrutinee`,
      -- permuting internally) so the args at use sites stay in
      -- SAW's order: `ite a b trueBranch falseBranch`.
      --
      -- The `rfl`-proven `iteDep_True` / `iteDep_False` lemmas in
      -- SAWCorePreludeExtra.lean catch any drift in the Lean-side
      -- permutation at lake build time. This Haskell-side test
      -- catches the complementary regression: the translator
      -- itself dropping or reordering args before they reach the
      -- Lean wrapper. A future change that retargets `mapsTo
      -- sawCorePreludeExtraModule "ite"` to `Bool.rec` directly
      -- would silently swap the True and False branches; this
      -- test forces such a change to be deliberate.
      boolTy <- scBoolType sc
      tBool  <- scBool sc True
      fBool  <- scBool sc False
      -- ite Bool true false true:
      --   args in SAW order are (Bool, true, false, true)
      --   semantic meaning: scrutinee=true picks trueBranch=false
      iteCall <- scGlobalApply sc "Prelude.ite"
                   [boolTy, tBool, fBool, tBool]
      s <- translateOrFail sc "iteOrder" iteCall
      -- Routing pin: emission goes through our wrapper, not bare
      -- Bool.rec.
      assertContains "routes to ite wrapper" "ite Bool" s
      assertNotContains "not Bool.rec directly" "Bool.rec" s
      -- Arg-order pin: (Bool, true, false, true) preserved in
      -- SAW's order. If the translator were to reorder args
      -- (passing falseBranch before trueBranch), the emitted
      -- subsequence would change.
      assertContains "preserves SAW arg order"
                     "ite Bool Bool.true Bool.false Bool.true" s
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
