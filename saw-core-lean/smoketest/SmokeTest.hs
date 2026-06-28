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
                  ( auditPreludePrimitivesForLean
                  , auditOpaqueBuiltinsCoveredBySpecialTreatment
                  , discoverNatRecReachers
                  , iterateNormalizeToFixedPoint
                  , scNormalizeForLean
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
      -- Audit P-1 (2026-05-06): the let-RHS is parenthesized to
      -- bulletproof Lean's column-sensitive parser when the RHS
      -- breaks across lines. So the rendered form is `let x := (7)`,
      -- not `let x := 7`. The pattern checks the parenthesized form.
      assertContains    "let x := (7)"      "let x := (7)" s

  , testCase "List prints with commas" $ do
      let body = Lean.List [Lean.NatLit 1, Lean.NatLit 2, Lean.NatLit 3]
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "xs" [] Nothing body))
      assertContains "list" "[1, 2, 3]" s

  , testCase "StringLit escapes double quotes and backslashes" $ do
      let body = Lean.StringLit "a\"b\\c"
          s    = render (Lean.prettyDecl (Lean.Definition Lean.Computable [] "msg" [] Nothing body))
      assertContains "string escape" "\"a\\\"b\\\\c\"" s

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

mkErrorAt :: SharedContext -> Term -> String -> IO Term
mkErrorAt sc resultTy msg = do
  msgTerm <- scString sc (Text.pack msg)
  scGlobalApply sc "Prelude.error" [resultTy, msgTerm]

mkBoolError :: SharedContext -> String -> IO Term
mkBoolError sc msg = do
  boolTy <- scBoolType sc
  mkErrorAt sc boolTy msg

translatorTests :: SharedContext -> TestTree
translatorTests sc = testGroup "SAWCoreLean.Term"
  [ testCase "\\(x : Bool) -> x" $ do
      boolTy <- scBoolType sc
      xName  <- scFreshVarName sc "x"
      xVar   <- scVariable   sc xName boolTy
      idBool <- scLambda     sc xName boolTy xVar
      s <- translateOrFail sc "identity" idBool
      assertContains "body"
        "def identity (x : Except String Bool) : Except String Bool" s
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

  , testCase "non-empty ArrayValue keeps wrapped shape in value arguments" $ do
      -- Non-empty arrays translate through vecSequenceM, whose result is
      -- Except-wrapped. If shape inference loses that fact, polymorphic
      -- value consumers such as PairValue receive an Except term where a raw
      -- vector is expected.
      boolTy   <- scBoolType sc
      true     <- scBool sc True
      one      <- scNat sc 1
      vec1Bool <- scGlobalApply sc "Prelude.Vec" [one, boolTy]
      arrayTm  <- scVector sc boolTy [true]
      pairTm   <- scGlobalApply sc "Prelude.PairValue"
                    [vec1Bool, vec1Bool, arrayTm, arrayTm]
      s <- translateOrFail sc "arrayShapePair" pairTm
      assertContains "binds sequenced vector before PairValue"
                     "Bind.bind x__" s
      assertContains "shared RHS preserves sequenced vector"
                     "let x__ := (vecSequenceM" s
      assertContains "then applies PairValue to raw bound values"
                     "@PairType.PairValue" s

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

  , testCase "closed binary Nat constructor chain emits Lean helper chain" $ do
      boolTy <- scBoolType sc
      one <- scGlobalApply sc "Prelude.One" []
      twoPos <- scGlobalApply sc "Prelude.Bit0" [one]
      fourPos <- scGlobalApply sc "Prelude.Bit0" [twoPos]
      four <- scGlobalApply sc "Prelude.NatPos" [fourPos]
      vec4Bool <- scGlobalApply sc "Prelude.Vec" [four, boolTy]
      xsName <- scFreshVarName sc "xs"
      xsVar <- scVariable sc xsName vec4Bool
      lam <- scLambda sc xsName vec4Bool xsVar
      out <- translateOrFail sc "closedBinaryNat" lam
      assertContains "NatPos helper remains visible"
                     "CryptolToLean.SAWCorePrimitives.natPos_macro" out
      assertContains "Bit0 helper remains visible"
                     "CryptolToLean.SAWCorePrimitives.bit0_macro" out
      assertNotContains "Haskell no longer collapses to compact Nat literal"
                        "Vec 4 Bool" out

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

  , testCase "every leanOpaqueBuiltins entry has SpecialTreatment (L-14 companion)" $ do
      -- Catches the divNat/modNat bug class: a Prelude def that's in
      -- 'leanOpaqueBuiltins' (kept opaque during normalization) but
      -- missing a SpecialTreatment entry. Without a mapping, the
      -- translator emits the raw SAW Prelude namespace
      -- ('CryptolToLean.SAWCorePrelude.divNat') which doesn't resolve
      -- at Lean elaboration time — silently producing a .lean file
      -- that fails to compile.
      --
      -- L-14 proper only checks SAW 'primitive' decls (no body).
      -- Named defs in 'leanOpaqueBuiltins' have bodies and escape
      -- that check; this companion closes the gap.
      missing <- auditOpaqueBuiltinsCoveredBySpecialTreatment sc defaultConfig
      case missing of
        []  -> pure ()
        ms  -> assertFailure $
          "leanOpaqueBuiltins entries lacking SpecialTreatment in Prelude:\n  " ++
          unwords (map Text.unpack ms) ++
          "\nAdd a mapsTo entry in " ++
          "saw-core-lean/src/SAWCoreLean/SpecialTreatment.hs for each, " ++
          "and define the corresponding Lean function in SAWCorePrimitives.lean."

  , testCase "every Prelude primitive is mapped or intentional (L-14)" $ do
      -- L-14 lockdown. Every SAW Prelude primitive (def with no
      -- body) needs either a SpecialTreatment entry or an explicit
      -- entry in 'leanIntentionallyUnmappedPrimitives'. Otherwise
      -- a translated term referencing it would fail at Lean
      -- elaboration with "unknown identifier".
      --
      -- This test catches new Prelude additions early: a fresh
      -- 'primitive newOp : ...' in Prelude.sawcore that nobody
      -- maps fails this test rather than waiting for a downstream
      -- Cryptol demo to surface the gap.
      (_covered, missing) <- auditPreludePrimitivesForLean sc defaultConfig
      case missing of
        []  -> pure ()
        ms  -> assertFailure $
          "SAW Prelude primitive(s) without SpecialTreatment or " ++
          "intentional-unmapped exception:\n  " ++
          unwords (map Text.unpack ms) ++
          "\nAdd a SpecialTreatment entry in " ++
          "saw-core-lean/src/SAWCoreLean/SpecialTreatment.hs, or " ++
          "extend 'leanIntentionallyUnmappedPrimitives' in " ++
          "saw-central/src/SAWCentral/Prover/Exporter.hs with a reason."

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
      -- Re-architecture moved higher-universe handling into a
      -- per-binder universe model, so the generated declaration may
      -- be universe-polymorphic. This test pins the body contract:
      -- a SAW term that IS sort 0
      -- (i.e. the 'Type 0' universe expression) renders as 'Type'
      -- in Lean.
      sort0 <- scSort sc (mkSort 0)
      s <- translateOrFail sc "ty" sort0
      assertContains "sort 0 → Type" "Type" s
      -- Specifically: we don't drift to a numeric universe.
      assertNotContains "no Type 1 leak" "Type 1" s

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

  , testCase "scNormalize cap is set to 100 iterations (L-6 doc pin)" $ do
      -- Pin the documented cap value. If somebody bumps it (or
      -- drops it), this test forces them to update both the
      -- constant and the soundness doc that cites it. Cheap
      -- documentation-vs-code consistency check.
      assertBool "max iters constant is 100"
                 (scNormalizeForLeanMaxIters == 100)

  , testCase "Bool#rec doesn't surface bare in translated output (L-16)" $ do
      -- L-16 lockdown. SAW's Bool data declaration is True-first;
      -- Lean's auto-generated Bool.rec is False-first. Bool#rec
      -- emitted bare (e.g. via scNormalize unfolding ite/iteDep)
      -- silently swaps trueCase/falseCase at the Lean side.
      -- Pre-L-16, every test using if/then/else was emitting a
      -- swapped Bool.rec.
      --
      -- The fix: keep ite/iteDep/iteDep_True/iteDep_False/
      -- ite_eq_iteDep opaque under scNormalize so they don't
      -- unfold to bare Bool#rec1; the surface stays at the
      -- wrapper level and routes via SpecialTreatment to the
      -- handwritten Lean wrapper that permutes correctly. This
      -- test pins that no translator-emitted output ever contains
      -- bare '@Bool.rec' for terms that originally went through
      -- ite. (Direct Bool#rec from parse_core / hand-constructed
      -- terms is a separate case — not currently emitted by any
      -- demo Cryptol code, but documented in soundness-boundaries
      -- as a known gap until either the translator permutes at
      -- emission or such terms get rejected.)
      --
      -- Construct: 'ite Bool b x y' on Cryptol-shape Bool args.
      boolTy <- scBoolType sc
      bName  <- scFreshVarName sc "b"
      bVar   <- scVariable sc bName boolTy
      xName  <- scFreshVarName sc "x"
      xVar   <- scVariable sc xName boolTy
      yName  <- scFreshVarName sc "y"
      yVar   <- scVariable sc yName boolTy
      iteCall <- scGlobalApply sc "Prelude.ite" [boolTy, bVar, xVar, yVar]
      -- Wrap in lambdas so the type-checks.
      lam1 <- scLambda sc yName boolTy iteCall
      lam2 <- scLambda sc xName boolTy lam1
      lam3 <- scLambda sc bName boolTy lam2
      s <- translateOrFail sc "iteOpacity" lam3
      -- The emission must route via our handwritten 'ite' wrapper,
      -- not unfold to bare Bool.rec.
      assertContains "routes via ite wrapper"
                     "CryptolToLean.SAWCorePreludeExtra.ite" s
      assertNotContains "no bare Bool.rec leaked through"
                        "Bool.rec" s

  , testCase "SAW Bool ops (not/and/or/xor/boolEq) don't leak Bool.rec (L-16 follow-up)" $ do
      -- Phase 3a follow-up to L-16. The review of Phase 1a flagged
      -- a comment-grade guarantee in Exporter.hs's leanOpaqueBuiltins:
      -- "not / and / or / xor / boolEq use ite internally; one
      -- unfolding step gets them to ite which is opaque, so they
      -- don't reach Bool#rec." Without a test, that claim is
      -- the kind of thing the lockdown principle expressly warns
      -- about. This pins it: every Bool prelude op, AFTER the
      -- 'scNormalizeForLean' pass that runs in real workflows,
      -- surfaces at the ite layer, never at bare Bool.rec.
      --
      -- Audit (2026-05-07): the prior version of this test skipped
      -- normalization and relied on the unmapped-default
      -- 'UsePreserve' silently emitting 'CryptolToLean.SAWCorePrelude.not'
      -- (which doesn't contain "Bool.rec"). That was a vacuous pass
      -- — the dangling reference was junk that wouldn't elaborate.
      -- Now: normalize first (matching the real pipeline), assert
      -- the normalized form translates without 'Bool.rec'.
      boolTy <- scBoolType sc
      bName  <- scFreshVarName sc "b"
      bVar   <- scVariable sc bName boolTy
      cName  <- scFreshVarName sc "c"
      cVar   <- scVariable sc cName boolTy
      let probe lbl mkApp = do
            t <- mkApp
            wrappedInner <- scLambda sc cName boolTy t
            wrapped      <- scLambda sc bName boolTy wrappedInner
            normalized   <- scNormalizeForLean sc [] wrapped
            s <- translateOrFail sc lbl normalized
            assertNotContains
              (lbl ++ ": Bool.rec leaked through " ++ lbl) "Bool.rec" s
      probe "Prelude.not"     (scGlobalApply sc "Prelude.not"    [bVar])
      probe "Prelude.and"     (scGlobalApply sc "Prelude.and"    [bVar, cVar])
      probe "Prelude.or"      (scGlobalApply sc "Prelude.or"     [bVar, cVar])
      probe "Prelude.xor"     (scGlobalApply sc "Prelude.xor"    [bVar, cVar])
      probe "Prelude.boolEq"  (scGlobalApply sc "Prelude.boolEq" [bVar, cVar])

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
      assertContains "routes to iteM wrapper" "iteM Bool" s
      assertNotContains "not Bool.rec directly" "Bool.rec" s
      -- Arg-order pin: (Bool, true, false, true) preserved in
      -- SAW's order. If the translator were to reorder args
      -- (passing falseBranch before trueBranch), the emitted
      -- subsequence would change.
      assertContains "preserves SAW arg order"
                     "iteM Bool (Pure.pure Bool.true) (Pure.pure\n  Bool.false) (Pure.pure Bool.true)" s

  , testCase "Nat value result binds before raw-Nat variable function arg" $ do
      -- Phase beta Nat discipline. Nat values are raw when used as type
      -- indices, but value computations such as bvToNat can still fail
      -- through their value inputs and therefore produce wrapped Nat.
      -- When such a wrapped Nat is supplied to a raw Nat formal
      -- (representative: Stream.rec's case binder s : Nat -> α), the
      -- application must bind the Nat before calling the function.
      natTy <- scNatType sc
      boolTy <- scBoolType sc
      width <- scNat sc 8
      zero <- scNat sc 0
      bvZero <- scGlobalApply sc "Prelude.bvNat" [width, zero]
      idx <- scGlobalApply sc "Prelude.bvToNat" [width, bvZero]
      iName <- scFreshVarName sc "i"
      sTy <- scPi sc iName natTy boolTy
      sName <- scFreshVarName sc "s"
      sVar <- scVariable sc sName sTy
      app <- scApply sc sVar idx
      lam <- scLambda sc sName sTy app
      out <- translateOrFail sc "natValueArg" lam
      assertContains "bvToNat result is lifted"
                     "Pure.pure" out
      assertContains "bvToNat consumes helper-chain Nat width"
                     "bvToNat (CryptolToLean.SAWCorePrimitives.natPos_macro" out
      assertContains "bvToNat consumes the bound bitvector"
                     "v_1))) (fun v_0 => s v_0)" out
      assertContains "wrapped Nat is bound before raw call"
                     "fun v_0 => s v_0" out
      assertNotContains "no monadic Nat passed directly to s"
                        "s (Bind.bind" out

  , testCase "MkStream emits totality obligation for pure index functions" $ do
      boolTy <- scBoolType sc
      true <- scBool sc True
      natTy <- scNatType sc
      iName <- scFreshVarName sc "i"
      idxFn <- scLambda sc iName natTy true
      mkStreamApp <- scGlobalApply sc "Prelude.MkStream" [boolTy, idxFn]
      out <- translateOrFail sc "mkStreamWrappedIndex" mkStreamApp
      assertContains "emits totality obligation"
                     "h_mkStream_total_obligation_" out
      assertContains "uses MkStream chooser"
                     "saw_mkStream_choose Bool" out
      assertContains "preserves pure body in the obligation"
                     "Pure.pure Bool.true" out

  , testCase "MkStream totality obligation preserves captured inputs" $ do
      boolTy <- scBoolType sc
      natTy <- scNatType sc
      xName <- scFreshVarName sc "x"
      xVar <- scVariable sc xName boolTy
      iName <- scFreshVarName sc "i"
      idxFn <- scLambda sc iName natTy xVar
      mkStreamApp <- scGlobalApply sc "Prelude.MkStream" [boolTy, idxFn]
      lam <- scLambda sc xName boolTy mkStreamApp
      out <- translateOrFail sc "mkStreamHoistsCaptured" lam
      assertContains "emits totality obligation"
                     "h_mkStream_total_obligation_" out
      assertContains "index function still sees the captured value"
                     "fun (i : Nat) => x" out
      assertContains "uses MkStream chooser"
                     "saw_mkStream_choose Bool" out

  , testCase "MkStream residual per-index effects emit totality obligation" $ do
      boolTy <- scBoolType sc
      natTy <- scNatType sc
      argName <- scFreshVarName sc "n"
      fTy <- scPi sc argName natTy boolTy
      fName <- scFreshVarName sc "f"
      fVar <- scVariable sc fName fTy
      iName <- scFreshVarName sc "i"
      iVar <- scVariable sc iName natTy
      body <- scApply sc fVar iVar
      idxFn <- scLambda sc iName natTy body
      mkStreamApp <- scGlobalApply sc "Prelude.MkStream" [boolTy, idxFn]
      lam <- scLambda sc fName fTy mkStreamApp
      out <- translateOrFail sc "mkStreamTotalityObligation" lam
      assertContains "emits totality obligation"
                     "h_mkStream_total_obligation_" out
      assertContains "uses MkStream chooser"
                     "saw_mkStream_choose Bool" out
      assertContains "contract mentions pointwise totality"
                     "saw_mkStream_total_exists Bool" out

  , testCase "MkStream index-dependent Prelude.error branches emit totality obligation" $ do
      boolTy <- scBoolType sc
      natTy <- scNatType sc
      zero <- scNat sc 0
      true <- scBool sc True
      boom <- mkBoolError sc "stream index error"
      iName <- scFreshVarName sc "i"
      iVar <- scVariable sc iName natTy
      cond <- scGlobalApply sc "Prelude.equalNat" [iVar, zero]
      body <- scGlobalApply sc "Prelude.ite" [boolTy, cond, boom, true]
      idxFn <- scLambda sc iName natTy body
      mkStreamApp <- scGlobalApply sc "Prelude.MkStream" [boolTy, idxFn]
      out <- translateOrFail sc "mkStreamIndexErrorObligation" mkStreamApp
      assertContains "emits totality obligation"
                     "h_mkStream_total_obligation_" out
      assertContains "preserves error branch in obligation"
                     "saw_throw_error Bool" out
      assertContains "uses MkStream chooser"
                     "saw_mkStream_choose Bool" out

  , testCase "Prelude.error raw/type/proof/function results emit obligations" $ do
      boolTy <- scBoolType sc
      natTy <- scNatType sc
      typeSort <- scSort sc (mkSort 0)
      true <- scBool sc True
      false <- scBool sc False
      eqProp <- scGlobalApply sc "Prelude.Eq" [boolTy, true, false]
      bName <- scFreshVarName sc "b"
      funTy <- scPi sc bName boolTy boolTy

      errNat <- mkErrorAt sc natTy "raw Nat error"
      natOut <- translateOrFail sc "errorNatObligation" errNat
      assertContains "Nat error has unreachable obligation"
                     "h_raw_error_obligation_ : (Prop) := (False)" natOut
      assertContains "Nat error uses False.elim"
                     "@False.elim Nat" natOut
      assertContains "Nat error uses obligation proof"
                     "h_raw_error_" natOut
      assertNotContains "Nat error is not wrapped Except"
                        "saw_throw_error Nat" natOut

      errType <- mkErrorAt sc typeSort "type error"
      typeOut <- translateOrFail sc "errorTypeObligation" errType
      assertContains "type error has unreachable obligation"
                     "h_raw_error_obligation_ : (Prop) := (False)" typeOut
      assertContains "type error uses False.elim"
                     "@False.elim Type" typeOut

      errProof <- mkErrorAt sc eqProp "proof error"
      proofOut <- translateOrFail sc "errorProofObligation" errProof
      assertContains "proof error has unreachable obligation"
                     "h_raw_error_obligation_ : (Prop) := (False)" proofOut
      assertContains "proof error uses False.elim"
                     "@False.elim (@Eq" proofOut
      assertContains "proof error proposition is preserved"
                     "(Pure.pure Bool.true) (Pure.pure Bool.false)" proofOut

      errFn <- mkErrorAt sc funTy "function error"
      fnOut <- translateOrFail sc "errorFunctionObligation" errFn
      assertContains "function error has unreachable obligation"
                     "h_raw_error_obligation_ : (Prop) := (False)" fnOut
      assertContains "function error uses False.elim"
                     "@False.elim" fnOut
      assertContains "function type is preserved"
                     "((b : Except String Bool) -> Except String Bool)" fnOut

  , testCase "RecordValue function field keeps datatype-parameter shape" $ do
      boolTy <- scBoolType sc
      xName <- scFreshVarName sc "x"
      xVar <- scVariable sc xName boolTy
      yName <- scFreshVarName sc "y"
      inner <- scLambda sc yName boolTy xVar
      fieldFn <- scLambda sc xName boolTy inner
      recordVal <- scRecordValue sc [("eq", fieldFn)]
      out <- translateOrFail sc "recordFunctionField" recordVal
      assertContains "record constructor emitted"
                     "@RecordType.RecordValue" out
      assertContains "function field first arg is wrapped"
                     "fun (x : Except String" out
      assertContains "function field second arg is wrapped"
                     "(y : Except String" out
      assertNotContains "function field is not bound as an Except value"
                        "Bind.bind (fun (x : Except String Bool)" out

  , testCase "Eq.rec proof supplied to coerce stays raw" $ do
      typeSort <- scSort sc (mkSort 0)
      boolTy <- scBoolType sc
      true <- scBool sc True
      eqDef <- scGlobalDef sc "Prelude.Eq"
      eqName <- case unwrapTermF eqDef of
        Constant nm -> pure nm
        _ -> assertFailure "Prelude.Eq did not resolve to a Constant"
      eqRec <- scRecursor sc eqName (mkSort 1)
      refl <- scGlobalApply sc "Prelude.Refl" [typeSort, boolTy]
      yName <- scFreshVarName sc "y"
      yVar <- scVariable sc yName typeSort
      eqYTy <- scGlobalApply sc "Prelude.Eq" [typeSort, boolTy, yVar]
      eqName' <- scFreshVarName sc "eq"
      motiveBody <- scLambda sc eqName' eqYTy eqYTy
      motive <- scLambda sc yName typeSort motiveBody
      eqProof <- scApplyAll sc eqRec
                   [typeSort, boolTy, motive, refl, boolTy, refl]
      coerced <- scGlobalApply sc "Prelude.coerce"
                   [boolTy, boolTy, eqProof, true]
      out <- translateOrFail sc "coerceEqRecProof" coerced
      assertContains "coerce receives Eq.rec proof"
                     "coerce Bool Bool (@Eq.rec" out
      assertNotContains "proof recursor is not monad-bound"
                        "Bind.bind (@Eq.rec" out

  , testCase "StreamCorec-shaped fix emits generic fixed-point obligation" $ do
      -- Haskell does not classify this recursive body as a special
      -- stream recurrence. It emits the literal fixed-point contract,
      -- while the nested MkStream emits its own totality contract:
      --   fix (Stream Bool) (\rec : Stream Bool -> MkStream Bool (\i -> True))
      boolTy       <- scBoolType sc
      true         <- scBool sc True
      natTy        <- scNatType sc
      streamBoolTy <- scGlobalApply sc "Prelude.Stream" [boolTy]
      iName        <- scFreshVarName sc "i"
      idxFn        <- scLambda sc iName natTy true       -- \i -> True
      mkStreamApp  <- scGlobalApply sc "Prelude.MkStream" [boolTy, idxFn]
      recName      <- scFreshVarName sc "rec"
      bodyLam      <- scLambda sc recName streamBoolTy mkStreamApp
      fixApp       <- scGlobalApply sc "Prelude.fix" [streamBoolTy, bodyLam]
      s <- translateOrFail sc "streamConst" fixApp
      assertContains "emits fixed-point contract" "saw_fix_unique_exists" s
      assertContains "chooses fixed point from proof" "saw_fix_choose" s
      assertContains "emits nested stream totality contract"
                     "saw_mkStream_total_exists" s
      assertContains "chooses stream from totality proof"
                     "saw_mkStream_choose" s
      assertNotContains "does not emit legacy stream helper" "mkStreamFix" s
      assertNotContains "no bare Prelude.fix in output" "Prelude.fix" s
      assertNotContains "no bare error path leak" "RejectedPrimitive" s

  , testCase "StreamCorec fix index-dependent Prelude.error branches emit unique-fix obligation" $ do
      boolTy <- scBoolType sc
      natTy <- scNatType sc
      zero <- scNat sc 0
      true <- scBool sc True
      streamBoolTy <- scGlobalApply sc "Prelude.Stream" [boolTy]
      boom <- mkBoolError sc "stream fix index error"
      iName <- scFreshVarName sc "i"
      iVar <- scVariable sc iName natTy
      cond <- scGlobalApply sc "Prelude.equalNat" [iVar, zero]
      idxBody <- scGlobalApply sc "Prelude.ite" [boolTy, cond, boom, true]
      idxFn <- scLambda sc iName natTy idxBody
      mkStreamApp <- scGlobalApply sc "Prelude.MkStream" [boolTy, idxFn]
      recName <- scFreshVarName sc "rec"
      bodyLam <- scLambda sc recName streamBoolTy mkStreamApp
      fixApp <- scGlobalApply sc "Prelude.fix" [streamBoolTy, bodyLam]
      out <- translateOrFail sc "streamFixIndexErrorObligation" fixApp
      assertContains "emits unique fixed-point obligation"
                     "h_fix_unique_obligation_" out
      assertContains "uses fixed-point chooser"
                     "saw_fix_choose" out
      assertContains "preserves error branch in obligation"
                     "saw_throw_error Bool" out

  , testCase "Phase 6: Float / Double primitives covered (no L-14 miss)" $ do
      -- SAW Prelude declares Float and Double as opaque types with
      -- mkFloat / mkDouble constructors. Phase 6 binds them as
      -- axioms in SAWCorePrimitives.lean. Cryptol's `Float e p`
      -- doesn't lower through these today (cryptol-saw-core punts
      -- to 'error UnitType "Unimplemented"'), so the binding is
      -- exercised only by parse_core / LLVM-extract paths. The
      -- L-14 startup audit is the gate that pins the routing —
      -- if Float/Double weren't mapped or in the unmapped list,
      -- this test would fail along with the existing L-14 audit.
      (_covered, missing) <- auditPreludePrimitivesForLean sc defaultConfig
      let needNames = ["Float", "Double", "mkFloat", "mkDouble"] :: [Text.Text]
      sequence_
        [ assertBool ("missing primitive: " ++ Text.unpack nm)
                     (nm `notElem` missing)
        | nm <- needNames ]

  , testCase "Phase 5c / Slice C: streamScanl routes via SAWCorePreludeExtra" $ do
      -- streamScanl is the only SAW Prelude def using Prelude.fix.
      -- Pre-Slice-C, scNormalize would unfold it into a large recursive
      -- term. Slice C keeps it opaque (leanOpaqueBuiltins) and routes via
      -- SpecialTreatment to the handwritten Lean equivalent in
      -- SAWCorePreludeExtra.
      --
      -- Audit (2026-05-07): apply scNormalizeForLean before
      -- translating. Pre-audit, the test skipped normalization, and
      -- relied on the now-removed silent UsePreserve fallback to
      -- emit 'Prelude.or' as a dangling 'CryptolToLean.SAWCorePrelude.or'
      -- ref. With the new "never drop errors" default, unmapped
      -- 'or' is now a hard reject; normalization unfolds it to
      -- 'ite' (which IS mapped) before translation, mirroring the
      -- real workflow.
      boolTy       <- scBoolType sc
      false        <- scBool sc False
      streamBoolTy <- scGlobalApply sc "Prelude.Stream" [boolTy]
      orFn         <- scGlobalApply sc "Prelude.or" []
      xsName       <- scFreshVarName sc "xs"
      xsVar        <- scVariable sc xsName streamBoolTy
      scanlCall    <- scGlobalApply sc "Prelude.streamScanl"
                        [boolTy, boolTy, orFn, false, xsVar]
      lam <- scLambda sc xsName streamBoolTy scanlCall
      normalized <- scNormalizeForLean sc [] lam
      s <- translateOrFail sc "scanlTest" normalized
      assertContains "uses streamScanl name" "streamScanl" s
      assertNotContains "no Prelude.fix surface" "Prelude.fix" s
      assertNotContains "no rejection leak"     "RejectedPrimitive" s
      -- Routing target: our handwritten Lean def in
      -- CryptolToLean.SAWCorePreludeExtra. Allow either a fully-
      -- qualified or open-shortened reference.
      assertContains "routes to SAWCorePreludeExtra.streamScanl"
                     "SAWCorePreludeExtra.streamScanl" s

  , testCase "BoundedVecFold-shaped fix emits generic fixed-point obligation" $ do
      -- Synthetic shape:
      --   fix (Vec 5 Bool) (\rec : Vec 5 Bool -> gen 5 Bool (\i -> True))
      -- Body doesn't use rec; we still emit the generic proof-carrying
      -- fixed-point contract instead of recognizing a vector recurrence
      -- in Haskell.
      boolTy   <- scBoolType sc
      true     <- scBool sc True
      natTy    <- scNatType sc
      five     <- scNat sc 5
      vec5Bool <- scGlobalApply sc "Prelude.Vec" [five, boolTy]
      iName    <- scFreshVarName sc "i"
      idxFn    <- scLambda sc iName natTy true
      genApp   <- scGlobalApply sc "Prelude.gen" [five, boolTy, idxFn]
      recName  <- scFreshVarName sc "rec"
      bodyLam  <- scLambda sc recName vec5Bool genApp
      fixApp   <- scGlobalApply sc "Prelude.fix" [vec5Bool, bodyLam]
      s <- translateOrFail sc "vecFix" fixApp
      assertContains "emits fixed-point contract" "saw_fix_unique_exists" s
      assertContains "chooses fixed point from proof" "saw_fix_choose" s
      assertContains "preserves wrapped vector body" "genM" s
      assertContains "vector length remains a Lean helper chain"
                     "CryptolToLean.SAWCorePrimitives.natPos_macro" s
      assertNotContains "does not emit legacy vector helper" "genFixVecChecked" s
      assertNotContains "does not emit legacy vector helper" "genFixMChecked" s
      assertNotContains "no bare Prelude.fix in output" "Prelude.fix" s
      assertNotContains "no rejection leak" "RejectedPrimitive" s

  , testCase "PairStreamCorec-shaped fix emits generic fixed-point obligation" $ do
      -- Mutual-stream-shaped synthetic term:
      --   fix (PairType1 (Stream Bool) (Stream Bool))
      --       (\x -> PairValue1 _ _ (MkStream Bool (\i -> True))
      --                             (MkStream Bool (\i -> False)))
      -- The translator emits the generic fixed-point contract plus
      -- pointwise totality obligations for each nested MkStream.
      boolTy       <- scBoolType sc
      true         <- scBool sc True
      false        <- scBool sc False
      natTy        <- scNatType sc
      streamBoolTy <- scGlobalApply sc "Prelude.Stream" [boolTy]
      pairTy       <- scGlobalApply sc "Prelude.PairType1"
                        [streamBoolTy, streamBoolTy]
      iName        <- scFreshVarName sc "i"
      idxFn1       <- scLambda sc iName natTy true
      idxFn2       <- scLambda sc iName natTy false
      mkStream1    <- scGlobalApply sc "Prelude.MkStream" [boolTy, idxFn1]
      mkStream2    <- scGlobalApply sc "Prelude.MkStream" [boolTy, idxFn2]
      pairValue    <- scGlobalApply sc "Prelude.PairValue1"
                        [streamBoolTy, streamBoolTy, mkStream1, mkStream2]
      xName        <- scFreshVarName sc "x"
      bodyLam      <- scLambda sc xName pairTy pairValue
      fixApp       <- scGlobalApply sc "Prelude.fix" [pairTy, bodyLam]
      s <- translateOrFail sc "pairStreams" fixApp
      assertContains "emits fixed-point contract" "saw_fix_unique_exists" s
      assertContains "chooses fixed point from proof" "saw_fix_choose" s
      assertContains "emits nested stream totality contract"
                     "saw_mkStream_total_exists" s
      assertContains "chooses stream from totality proof"
                     "saw_mkStream_choose" s
      assertNotContains "does not emit legacy pair-stream helper"
                        "mkStreamFixPair" s
      assertNotContains "no Prelude.fix leak" "Prelude.fix" s
      assertNotContains "no rejection" "RejectedPrimitive" s

  , testCase "polymorphic stream iterate fix emits generic obligation" $ do
      typeSort <- scSort sc (mkSort 0)
      boolTy <- scBoolType sc
      true <- scBool sc True
      natTy <- scNatType sc

      aName <- scFreshVarName sc "a"
      aVar <- scVariable sc aName typeSort
      stepName <- scFreshVarName sc "step"
      stepArgName <- scFreshVarName sc "stepArg"
      stepTy <- scPi sc stepArgName aVar aVar
      seedName <- scFreshVarName sc "seed"
      streamA <- scGlobalApply sc "Prelude.Stream" [aVar]
      typeArg <- scPi sc aName typeSort =<<
                 scPi sc stepName stepTy =<<
                 scPi sc seedName aVar streamA

      bodyAName <- scFreshVarName sc "a"
      bodyAVar <- scVariable sc bodyAName typeSort
      bodyStepName <- scFreshVarName sc "step"
      bodyStepArgName <- scFreshVarName sc "stepArg"
      bodyStepTy <- scPi sc bodyStepArgName bodyAVar bodyAVar
      bodySeedName <- scFreshVarName sc "seed"
      bodySeedVar <- scVariable sc bodySeedName bodyAVar
      idxName <- scFreshVarName sc "i"
      idxFn <- scLambda sc idxName natTy bodySeedVar
      mkStreamApp <- scGlobalApply sc "Prelude.MkStream" [bodyAVar, idxFn]
      recName <- scFreshVarName sc "rec"
      bodyArg <- scLambdaList sc
        [ (recName, typeArg)
        , (bodyAName, typeSort)
        , (bodyStepName, bodyStepTy)
        , (bodySeedName, bodyAVar)
        ]
        mkStreamApp

      bName <- scFreshVarName sc "b"
      stepArg <- scLambda sc bName boolTy true
      fixApp <- scGlobalApply sc "Prelude.fix"
        [typeArg, bodyArg, boolTy, stepArg, true]
      s <- translateOrFail sc "iterateNoBroadRewrite" fixApp
      assertContains "emits generic raw fixed-point obligation"
                     "saw_fix_unique_exists_raw" s
      assertNotContains "does not rewrite to cryptolIterate"
                        "cryptolIterate" s

  , testCase "Phase 5: unmatched fix shapes emit unique-fix obligations" $ do
      -- Conservatism check after proof-carrying fix migration. The
      -- recognizer still only computes audited productive shapes
      -- directly. A fix over Bool falls back to a Lean obligation
      -- requiring existence and uniqueness of a fixed point; Haskell
      -- does not fabricate a value or postulate an axiom.
      boolTy  <- scBoolType sc
      bName   <- scFreshVarName sc "b"
      bVar    <- scVariable sc bName boolTy
      idLam   <- scLambda sc bName boolTy bVar
      fixApp  <- scGlobalApply sc "Prelude.fix" [boolTy, idLam]
      out <- translateOrFail sc "fixIdObligation" fixApp
      assertContains "emits unique fixed-point obligation"
                     "h_fix_unique_obligation_" out
      assertContains "contract is over Bool"
                     "saw_fix_unique_exists Bool" out
      assertContains "uses fixed-point chooser"
                     "saw_fix_choose" out
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
