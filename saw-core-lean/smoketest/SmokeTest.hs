{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Direct-link regression tests for the Lean 4 backend. Each group
below targets a specific layer (pretty-printer, translator, goal
emission) so a failure's cause is obvious from the test name.
-}

module Main (main) where

import           Data.List           (isInfixOf, isPrefixOf, tails)
import qualified Data.Text           as Text
import qualified Language.Lean.AST   as Lean
import qualified Language.Lean.Pretty as Lean
import           Prettyprinter        (Doc, defaultLayoutOptions, layoutPretty)
import           Prettyprinter.Render.String (renderString)

import           SAWCore.Prelude     (scLoadPreludeModule)
import qualified SAWCore.QualName    as QN
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
import           SAWCoreLean.Term (FixClass(..), classifyFixShape)

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

assertContainsSquashed :: String -> String -> String -> IO ()
assertContainsSquashed label needle haystack =
  assertContains label (unwords (words needle)) (unwords (words haystack))

assertNotContainsSquashed :: String -> String -> String -> IO ()
assertNotContainsSquashed label needle haystack =
  assertNotContains label (unwords (words needle)) (unwords (words haystack))

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
translateOrFail = translateWithConfigOrFail defaultConfig

translateWithConfigOrFail ::
  TranslationConfiguration -> SharedContext -> String -> Term -> IO String
translateWithConfigOrFail config sc label body = do
  bodyType <- scTypeOf sc body
  mm       <- scGetModuleMap sc
  case translateTermAsDeclImports config mm (Lean.Ident label) body bodyType of
    Right doc -> pure (render doc)
    Left err -> do
      msg <- ppTranslationError sc err
      assertFailure (label ++ ": translation failed: " ++ Text.unpack msg)

translateExpectReject :: SharedContext -> String -> Term -> IO String
translateExpectReject sc label body = do
  bodyType <- scTypeOf sc body
  mm       <- scGetModuleMap sc
  case translateTermAsDeclImports defaultConfig mm (Lean.Ident label) body bodyType of
    Left err -> Text.unpack <$> ppTranslationError sc err
    Right doc -> assertFailure (label ++ ": expected rejection, got:\n" ++ render doc)

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

  , testCase "imported constants require explicit Lean realization" $ do
      boolTy <- scBoolType sc
      extBool <- scOpaqueConstant sc
        (mkImportedName (QN.fromNameIndex QN.NamespaceFresh "extBool" 0))
        boolTy
      msg <- translateExpectReject sc "importedBoolRejected" extBool
      assertContains "rejection mentions explicit realization"
        "imported constants require an explicit Lean realization" msg

  , testCase "explicit imported value emits checked realization alias" $ do
      boolTy <- scBoolType sc
      extBool <- scOpaqueConstant sc
        (mkImportedName (QN.fromNameIndex QN.NamespaceFresh "extBoolRealized" 0))
        boolTy
      let config = defaultConfig { constantSkips = ["extBoolRealized"] }
      s <- translateWithConfigOrFail config sc "importedBoolRealized" extBool
      assertContains "realization alias"
        "def __saw_realizes_" s
      assertContainsSquashed "alias has wrapped contract"
        ": Except String Bool :=" s
      assertContains "alias uses external target"
        "extBoolRealized" s
      assertNotContains "main def does not re-wrap alias"
        "Pure.pure __saw_realizes_" s

  , testCase "explicit imported function uses shape-aware application" $ do
      boolTy <- scBoolType sc
      bName <- scFreshVarName sc "b"
      boolToBool <- scPi sc bName boolTy boolTy
      extNot <- scOpaqueConstant sc
        (mkImportedName (QN.fromNameIndex QN.NamespaceFresh "extNot" 0))
        boolToBool
      true <- scBool sc True
      app <- scApplyAll sc extNot [true]
      let config = defaultConfig { constantSkips = ["extNot"] }
      s <- translateWithConfigOrFail config sc "importedNotTrue" app
      assertContains "realization alias"
        "def __saw_realizes_" s
      assertContains "application adapts raw argument"
        "Pure.pure Bool.true" s
      assertContains "application calls alias"
        "__saw_realizes_" s

  , testCase "unsafeAssert emits explicit Eq proof obligation" $ do
      boolTy <- scBoolType sc
      true <- scBool sc True
      false <- scBool sc False
      asserted <- scGlobalApply sc "Prelude.unsafeAssert"
        [boolTy, true, false]
      s <- translateOrFail sc "unsafeAssertObligation" asserted
      assertContains "obligation name"
        "h_unsafeAssert_obligation_" s
      assertContainsSquashed "asserted proposition"
        "@Eq.{1} Bool Bool.true Bool.false" s
      assertNotContains "proof obligation does not invent wrapped carrier"
        "Except String Bool" s
      assertContains "rfl-first evidence script with loud sorry fallback"
        "by (first | rfl | skip); all_goals sorry" s
      assertNotContains "does not hide assertion in tactic"
        "saw_unsafeAssert" s

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
      assertContainsSquashed "bvToNat consumes helper-chain Nat width"
                     "bvToNat (CryptolToLean.SAWCorePrimitives.natPos_macro" out
      assertContainsSquashed "bvToNat consumes the bound bitvector"
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

  , testCase "Prelude.error raw results reject; wrapped-result functions lower" $ do
      -- Audited disposition (2026-07-14,
      -- doc/2026-07-14_reachable-raw-error-disposition.md): raw-result
      -- error (Nat/index, sort, proof, raw-result Pi) REJECTS — the
      -- retired h_raw_error_ : False contract was undischargeable at
      -- every reachable position. A non-dependent Pi with a
      -- value-domain final result lowers to the constant-error
      -- function through the same saw_throw_error route as a
      -- value-domain error, message preserved.
      boolTy <- scBoolType sc
      natTy <- scNatType sc
      typeSort <- scSort sc (mkSort 0)
      true <- scBool sc True
      false <- scBool sc False
      eqProp <- scGlobalApply sc "Prelude.Eq" [boolTy, true, false]
      bName <- scFreshVarName sc "b"
      funTy <- scPi sc bName boolTy boolTy

      errNat <- mkErrorAt sc natTy "raw Nat error"
      natMsg <- translateExpectReject sc "errorNatRejects" errNat
      assertContains "Nat error rejects at the raw position"
                     "demanded at a raw position" natMsg

      errType <- mkErrorAt sc typeSort "type error"
      typeMsg <- translateExpectReject sc "errorTypeRejects" errType
      assertContains "type error rejects at the raw position"
                     "demanded at a raw position" typeMsg

      errProof <- mkErrorAt sc eqProp "proof error"
      proofMsg <- translateExpectReject sc "errorProofRejects" errProof
      assertContains "proof error rejects at the raw position"
                     "demanded at a raw position" proofMsg

      errFn <- mkErrorAt sc funTy "function error"
      fnOut <- translateOrFail sc "errorFunctionConstant" errFn
      assertContains "function error lowers via saw_throw_error"
                     "saw_throw_error Bool" fnOut
      assertContainsSquashed "constant-error function formal at wrapped carrier"
                     "(η_err_arg_0 : Except String Bool)" fnOut
      assertNotContains "no False obligation remains"
                        "h_raw_error_" fnOut
      assertContainsSquashed "message is preserved at the wrapped carrier"
                     "(Pure.pure \"function error\")" fnOut

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
      assertContainsSquashed "function field first arg is wrapped"
                             "fun (x : Except String" out
      assertContainsSquashed "function field second arg is wrapped"
                             "(y : Except String" out
      assertNotContainsSquashed "function field is not bound as an Except value"
                                "Bind.bind (fun (x : Except String Bool)" out

  , testCase "partial ctor eta formals are instantiation-directed" $ do
      -- Debts slice: a var-headed formal's mode follows the SUPPLIED
      -- type actual ('instantiationMode'), not a blanket value-domain
      -- assumption. Partially apply PairValue at a := Bool -> Bool,
      -- b := Bool: the missing x-slot eta formal is a FUNCTION —
      -- spliced structurally into the ctor, never Bind.bind-bound as
      -- an Except value — while the missing y-slot eta formal is the
      -- phase-beta wrapped representation and binds. (The residual
      -- assumption would declare BOTH wrapped, emitting Bind.bind
      -- over a function — malformed Lean. Top-level partial
      -- applications never elaborate — eta binders are unannotated —
      -- so this pin lives here, not in an obligations row.)
      boolTy <- scBoolType sc
      bName <- scFreshVarName sc "b"
      fnTy <- scPi sc bName boolTy boolTy
      pairPartial <- scGlobalApply sc "Prelude.PairValue" [fnTy, boolTy]
      out <- translateOrFail sc "pairPartialFnInst" pairPartial
      assertContainsSquashed "value-slot eta formal binds"
                             "Bind.bind η_1" out
      assertContainsSquashed "function-slot eta formal splices raw"
                             "Bool η_0 v_3" out
      assertNotContainsSquashed "function-slot eta formal is not bound"
                                "Bind.bind η_0" out

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

  , testCase "coerce wrapped result keeps wrapped shape at Eq" $ do
      typeSort <- scSort sc (mkSort 0)
      boolTy <- scBoolType sc
      true <- scBool sc True
      refl <- scGlobalApply sc "Prelude.Refl" [typeSort, boolTy]
      coerced <- scGlobalApply sc "Prelude.coerce"
                   [boolTy, boolTy, refl, true]
      eqTerm <- scGlobalApply sc "Prelude.Eq" [boolTy, coerced, true]
      out <- translateOrFail sc "coerceWrappedEq" eqTerm
      assertContainsSquashed "Eq compares wrapped Bool values"
        "@Eq.{1} (Except String Bool) (Bind.bind (Pure.pure Bool.true)" out
      assertNotContainsSquashed "coerce result is not double-lifted"
        "Pure.pure (Bind.bind (Pure.pure Bool.true)" out

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
      msg <- translateExpectReject sc "streamConst" fixApp
      assertContains "R4: unrecognized wrapped fix rejects"
                     "unrecognized wrapped fix shape" msg
      assertContains "carries the recognizer reason"
                     "stream element body is not the seeded atWithDefault" msg

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
      msg <- translateExpectReject sc "streamFixIndexErrorObligation" fixApp
      assertContains "R4: unrecognized wrapped fix rejects"
                     "unrecognized wrapped fix shape" msg

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
      msg <- translateExpectReject sc "vecFix" fixApp
      assertContains "R4: unrecognized wrapped fix rejects"
                     "unrecognized wrapped fix shape" msg
      assertContains "carries the recognizer reason"
                     "gen element body is not an ite" msg

  , testCase "PairStreamCorec-shaped fix rejects with the amendment-D diagnostic" $ do
      -- Mutual-stream-shaped synthetic term:
      --   fix (PairType1 (Stream Bool) (Stream Bool))
      --       (\x -> PairValue1 _ _ (MkStream Bool (\i -> True))
      --                             (MkStream Bool (\i -> False)))
      -- R3b (fifth-audit amendment D): paired-stream mutual
      -- corecursion has its own disposition — an explicit NAMED
      -- rejection, never the retired-contract fallback and never a
      -- silently introduced lowering.
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
      msg <- translateExpectReject sc "pairStreams" fixApp
      assertContains "names the paired-stream disposition"
                     "paired-stream mutual corecursion is not realized" msg

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
      msg <- translateExpectReject sc "fixIdObligation" fixApp
      assertContains "R4: the Bool witness rejects by name"
                     "unrecognized wrapped fix shape" msg
      assertContains "carries the recognizer reason"
                     "outside Vec/Stream/paired-Stream: Bool" msg
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
-- Anti-regression source lint (plan Slice 7)
--------------------------------------------------------------------------------

-- | Backend source files the lint sweeps.
lintSourceFiles :: [FilePath]
lintSourceFiles =
  map ("saw-core-lean/src/" ++)
    [ "SAWCoreLean/Term.hs"
    , "SAWCoreLean/Convention.hs"
    , "SAWCoreLean/Contracts.hs"
    , "SAWCoreLean/FixRecognizer.hs"
    , "SAWCoreLean/Monad.hs"
    , "SAWCoreLean/SAWModule.hs"
    , "SAWCoreLean/CryptolModule.hs"
    , "SAWCoreLean/SpecialTreatment.hs"
    , "SAWCoreLean/Lean.hs"
    , "Language/Lean/AST.hs"
    , "Language/Lean/Pretty.hs"
    ]

-- | The Lean support library the emitted corpus imports. The
-- transport distinctness-invariant lint scans every file: the
-- invariant is about what T-emitted NAMES can reduce to, and any
-- support module can introduce an alias.
supportLibraryFiles :: [FilePath]
supportLibraryFiles =
  map ("saw-core-lean/lean/CryptolToLean/" ++)
    [ "SAWCorePrimitives.lean"
    , "SAWCoreVectors.lean"
    , "SAWCoreBitvectors.lean"
    , "SAWCoreBitvectors_proofs.lean"
    , "SAWCorePrelude_proofs.lean"
    , "SAWCorePreludeExtra.lean"
    , "SAWCoreCtorOrder.lean"
    ]

-- | Names of deleted heuristics that must never reappear in CODE
-- (comment lines — tombstone NOTEs — are exempt). Each entry names
-- the slice that deleted it.
lintForbiddenNames :: [(String, String)]
lintForbiddenNames =
  [ ("bindingShapeOfTerm",       "Slice 2: shape guessed from emitted Lean term AST")
  , ("bindingShapeOfLeanTermM",  "Slice 2: monadic emitted-AST shape guess")
  , ("translatedTermAsWrapped",  "Slice 2: wrap-status read off the emitted term")
  , ("CalleeTransitional",       "Slice 4c: the undeclared-convention escape hatch")
  , ("argumentBindPlan",         "Slice 4b: bind plan from emitted types, not declared modes")
  , ("polymorphicFormalInstantiatedExpected", "Slice 4b/debts: Pi-only instantiation predicate")
  , ("lowerRawLogicalCalleeRawMode", "debts slice: mode-guard over false raw-mode records")
  , ("equalityPropositionAtSubjectRep", "debts slice: surround-declared rho_eq entry point")
  , ("subjectRepFromTranslatedOperands", "Slice 5a: renamed to standaloneEqualitySubjectRep")
  , ("classifyRecursorResult",   "Slice 6.1: local recursor classification predicates")
  ]

-- | Allow-listed emitted-TYPE self-mirrors (documented
-- convention-internal classifiers of types the translator itself just
-- emitted). The ceiling is the current number of non-comment source
-- LINES mentioning the name; growing it means a NEW consumer was
-- added, which the plan forbids ("do not add new consumers").
-- Shrinking is always fine — lower the ceiling when you demote a use.
lintSelfMirrorCeilings :: [(String, Int)]
lintSelfMirrorCeilings =
  [ ("bindingShapeOfType", 7)   -- definition + binder-site Γ records
  , ("isExceptStringType", 5)   -- definition + bindingShapeOfType
                                -- + applyKnownFunctionWithShape result peel
  , ("peelLeanPiTypes",    6)   -- definition + the same result peel
  ]

-- | Non-comment source lines of a file (drops whole-line @--@
-- comments; block comments in these sources are file headers that
-- never mention the linted names).
lintCodeLines :: String -> [String]
lintCodeLines source =
  [ l | l <- lines source
      , not ("--" `isPrefixOf` dropWhile (== ' ') l) ]

antiRegressionLintTests :: TestTree
antiRegressionLintTests = testGroup "anti-regression source lint (Slice 7)"
  [ testCase "deleted heuristics stay deleted" $ do
      sources <- mapM readFile lintSourceFiles
      let hits =
            [ (file, name, why)
            | (file, source) <- zip lintSourceFiles sources
            , (name, why) <- lintForbiddenNames
            , any (name `isInfixOf`) (lintCodeLines source)
            ]
      assertBool
        ("resurrected deleted heuristic(s) — positions come from declared \
         \conventions and production records, never from emitted Lean: "
         ++ show hits)
        (null hits)
  , testCase "emitted-type self-mirrors gain no new consumers" $ do
      sources <- mapM readFile lintSourceFiles
      let allCode = concatMap lintCodeLines sources
          counts =
            [ (name, ceiling_, length (filter (name `isInfixOf`) allCode))
            | (name, ceiling_) <- lintSelfMirrorCeilings
            ]
          over_ = [ c | c@(_, ceil_, n) <- counts, n > ceil_ ]
      assertBool
        ("emitted-type self-mirror gained a consumer (name, ceiling, found): "
         ++ show over_ ++ " — classify from source types or declared \
         \conventions instead, or (if you demoted a use) lower the ceiling")
        (null over_)
  , testCase "support library defines no Except-headed type alias" $ do
      -- Transport distinctness invariant (2026-07-18/19 transport
      -- audits, binding condition 1): T never emits an
      -- Except-String-HEADED type, so the wrapped and raw readings
      -- of a SAW type are never defeq and every transport-mode
      -- mismatch is LOUD. A support-library TYPE ALIAS whose body
      -- head is `Except` (e.g. `abbrev Foo := Except String Bar`)
      -- would let a T-emitted name reduce to the carrier and reopen
      -- the corner SILENTLY. This scans every declaration body for
      -- an Except-headed right-hand side (whitespace-collapsed;
      -- named-argument uses like `(m := Except String)` are excluded
      -- by the preceding token's open paren).
      sources <- mapM readFile supportLibraryFiles
      let collapse = unwords . words . unlines . lintCodeLines
          hitsIn c =
            [ take 60 rest
            | (i, rest) <- zip [(0 :: Int) ..] (tails c)
            , any (`isPrefixOf` rest) [":= Except ", ":= (Except "]
            , let before = take i c
                  lastWord =
                    reverse (takeWhile (/= ' ')
                      (dropWhile (== ' ') (reverse before)))
            , not ("(" `isPrefixOf` lastWord)
            ]
          hits =
            [ (f, h)
            | (f, s) <- zip supportLibraryFiles sources
            , h <- hitsIn (collapse s)
            ]
      assertBool
        ("Except-headed definition body in the support library — this \
         \endangers the transport distinctness invariant (a type alias \
         \reducing to `Except String _` makes wrapped-vs-raw mode \
         \mismatches silently defeq): " ++ show hits)
        (null hits)
  , testCase "wrapExcept is the sole Except-carrier authority" $ do
      -- 2026-07-18 calculus/transport audits: BOTH backstops (the
      -- Prop backstop and the transport distinctness invariant —
      -- "T never emits Except-String-headed types") rest on the
      -- wrapping carrier being uniformly `Except String _`,
      -- constructed in exactly ONE place ('wrapExcept',
      -- Convention.hs) and recognized in exactly TWO
      -- ('isExceptStringType'; the telescope fingerprint's
      -- stripExcept). A NEW site mentioning the Except identifier
      -- means a new constructor or recognizer of the carrier —
      -- which must either route through wrapExcept or be added
      -- here DELIBERATELY with the backstop argument re-checked.
      sources <- mapM readFile lintSourceFiles
      let allCode = concatMap lintCodeLines sources
          n = length (filter ("\"Except\"" `isInfixOf`) allCode)
      assertBool
        ("Except-carrier mention count changed (found " ++ show n
         ++ ", ceiling 3: wrapExcept def + isExceptStringType + \
            \telescope stripExcept) — a new carrier \
            \constructor/recognizer endangers the Prop backstop and \
            \the transport distinctness invariant; route through \
            \wrapExcept or update this lint deliberately")
        (n <= 3)
  ]

--------------------------------------------------------------------------------
-- OP-3 successor recognizer (Slice R0 — inert; classification only)
--------------------------------------------------------------------------------

-- | Build the corpus's FUSED normalized Class-F body
--
-- > \rec -> gen 9 a (\i -> ite a (ltNat i 1)
-- >                            <seed>
-- >                            (at 8 a (gen 8 a (\i2 -> <elt i2>)) (subNat i 1)))
--
-- parameterized on the element function and the tail-selection index
-- so the negative cases can perturb exactly one discipline at a time.
-- Returns @(typeArg, bodyArg)@ for 'classifyFixShape'.
mkFusedFixF ::
  SharedContext ->
  (Term {- rec -} -> Term {- i2 -} -> IO Term)  {- element body -} ->
  (Term {- i -} -> IO Term)  {- tail-selection index -} ->
  IO (Term, Term)
mkFusedFixF sc mkElt mkTailIdx = do
  boolTy <- scBoolType sc
  natTy  <- scNatType sc
  n32    <- scNat sc 32
  n9     <- scNat sc 9
  n8     <- scNat sc 8
  n1     <- scNat sc 1
  n0     <- scNat sc 0
  elemTy <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
  vecTy  <- scGlobalApply sc "Prelude.Vec" [n9, elemTy]

  recName <- scFreshVarName sc "rec"
  recVar  <- scVariable sc recName vecTy
  iName   <- scFreshVarName sc "i"
  iVar    <- scVariable sc iName natTy
  i2Name  <- scFreshVarName sc "i2"
  i2Var   <- scVariable sc i2Name natTy

  elt      <- mkElt recVar i2Var
  innerF   <- scLambda sc i2Name natTy elt
  innerGen <- scGlobalApply sc "Prelude.gen" [n8, elemTy, innerF]
  tailIdx  <- mkTailIdx iVar
  tailB    <- scGlobalApply sc "Prelude.at" [n8, elemTy, innerGen, tailIdx]
  seedB    <- scGlobalApply sc "Prelude.bvNat" [n32, n0]
  cond     <- scGlobalApply sc "Prelude.ltNat" [iVar, n1]
  iteB     <- scGlobalApply sc "Prelude.ite" [elemTy, cond, seedB, tailB]
  genF     <- scLambda sc iName natTy iteB
  outerGen <- scGlobalApply sc "Prelude.gen" [n9, elemTy, genF]
  body     <- scLambda sc recName vecTy outerGen
  pure (vecTy, body)

shiftMinusOne :: SharedContext -> Term -> IO Term
shiftMinusOne sc iVar = do
  n1 <- scNat sc 1
  scGlobalApply sc "Prelude.subNat" [iVar, n1]

assertUnrecognized :: String -> FixClass -> IO ()
assertUnrecognized label verdict = case verdict of
  FixUnrecognized _ -> pure ()
  other -> assertFailure (label ++ ": expected FixUnrecognized, got "
                          ++ show other)

fixClassifierTests :: SharedContext -> TestTree
fixClassifierTests sc = testGroup "classifyFixShape (Slice R0, inert)"
  [ testCase "Bool-typed fix witness is Unrecognized" $ do
      boolTy <- scBoolType sc
      xName  <- scFreshVarName sc "x"
      xVar   <- scVariable sc xName boolTy
      body   <- scLambda sc xName boolTy xVar
      assertUnrecognized "Bool fix" (classifyFixShape boolTy body)

  , testCase "bare MkStream body without the seeded shape is Unrecognized" $ do
      -- R3a hardening: an arbitrary MkStream-headed body must NOT
      -- classify — only the canonical seeded single-step shape may
      -- (the corpus positive is the rec_ones golden trace).
      boolTy   <- scBoolType sc
      natTy    <- scNatType sc
      n32      <- scNat sc 32
      n0       <- scNat sc 0
      elemTy   <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
      streamTy <- scGlobalApply sc "Prelude.Stream" [elemTy]
      nName    <- scFreshVarName sc "n"
      elemBv   <- scGlobalApply sc "Prelude.bvNat" [n32, n0]
      stepF    <- scLambda sc nName natTy elemBv
      mk       <- scGlobalApply sc "Prelude.MkStream" [elemTy, stepF]
      recName  <- scFreshVarName sc "rec"
      body     <- scLambda sc recName streamTy mk
      assertUnrecognized "bare MkStream" (classifyFixShape streamTy body)

  , testCase "stream seed longer than 1 is Unrecognized" $ do
      boolTy   <- scBoolType sc
      natTy    <- scNatType sc
      n2       <- scNat sc 2
      streamTy <- scGlobalApply sc "Prelude.Stream" [boolTy]
      iName    <- scFreshVarName sc "i"
      iVar     <- scVariable sc iName natTy
      tt       <- scBool sc True
      seedV    <- scVector sc boolTy [tt, tt]
      elt      <- scGlobalApply sc "Prelude.atWithDefault"
                    [n2, boolTy, tt, seedV, iVar]
      stepF    <- scLambda sc iName natTy elt
      mk       <- scGlobalApply sc "Prelude.MkStream" [boolTy, stepF]
      recName  <- scFreshVarName sc "rec"
      body     <- scLambda sc recName streamTy mk
      assertUnrecognized "two-element stream seed"
        (classifyFixShape streamTy body)

  , testCase "computed (non-literal) length-1 stream seed is Unrecognized" $ do
      -- R3b review finding F1: the gate's seed guard must equal the
      -- lowering's destructure (literal single-element ArrayValue).
      -- A computed length-1 seed must classify Unrecognized at the
      -- gate, never surface as an internal-invariant error.
      boolTy   <- scBoolType sc
      natTy    <- scNatType sc
      n1       <- scNat sc 1
      streamTy <- scGlobalApply sc "Prelude.Stream" [boolTy]
      iName    <- scFreshVarName sc "i"
      iVar     <- scVariable sc iName natTy
      tt       <- scBool sc True
      jName    <- scFreshVarName sc "j"
      constF   <- scLambda sc jName natTy tt
      seedGen  <- scGlobalApply sc "Prelude.gen" [n1, boolTy, constF]
      elt      <- scGlobalApply sc "Prelude.atWithDefault"
                    [n1, boolTy, tt, seedGen, iVar]
      stepF    <- scLambda sc iName natTy elt
      mk       <- scGlobalApply sc "Prelude.MkStream" [boolTy, stepF]
      recName  <- scFreshVarName sc "rec"
      body     <- scLambda sc recName streamTy mk
      -- Pin the EXACT reason: the seed guard fires before the tail
      -- check, so this fails if the F1 guard is removed (the reason
      -- would flip to the tail diagnostic). assertUnrecognized alone
      -- would stay green via the tail check — no regression value
      -- (delta-review finding).
      case classifyFixShape streamTy body of
        FixUnrecognized reason ->
          reason @?= "stream seed is not a literal single-element vector"
        other ->
          assertFailure ("computed length-1 seed: expected \
            \FixUnrecognized, got " ++ show other)

  , testCase "stream selection at a non-binder index is Unrecognized" $ do
      boolTy   <- scBoolType sc
      natTy    <- scNatType sc
      n1       <- scNat sc 1
      n0       <- scNat sc 0
      streamTy <- scGlobalApply sc "Prelude.Stream" [boolTy]
      iName    <- scFreshVarName sc "i"
      tt       <- scBool sc True
      seedV    <- scVector sc boolTy [tt]
      elt      <- scGlobalApply sc "Prelude.atWithDefault"
                    [n1, boolTy, tt, seedV, n0]
      stepF    <- scLambda sc iName natTy elt
      mk       <- scGlobalApply sc "Prelude.MkStream" [boolTy, stepF]
      recName  <- scFreshVarName sc "rec"
      body     <- scLambda sc recName streamTy mk
      assertUnrecognized "constant selection index"
        (classifyFixShape streamTy body)

  , testCase "PairType1 of two Streams is Class S-paired" $ do
      boolTy   <- scBoolType sc
      n32      <- scNat sc 32
      elemTy   <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
      streamTy <- scGlobalApply sc "Prelude.Stream" [elemTy]
      pairTy   <- scGlobalApply sc "Prelude.PairType1" [streamTy, streamTy]
      recName  <- scFreshVarName sc "rec"
      recVar   <- scVariable sc recName pairTy
      body     <- scLambda sc recName pairTy recVar
      classifyFixShape pairTy body @?= FixClassSPaired

  , testCase "Vec fix with non-gen body is Unrecognized" $ do
      boolTy  <- scBoolType sc
      n9      <- scNat sc 9
      vecTy   <- scGlobalApply sc "Prelude.Vec" [n9, boolTy]
      recName <- scFreshVarName sc "rec"
      recVar  <- scVariable sc recName vecTy
      body    <- scLambda sc recName vecTy recVar
      assertUnrecognized "non-gen Vec body" (classifyFixShape vecTy body)

  , testCase "fused gen/ite recurrence is Class F" $ do
      (vecTy, body) <- mkFusedFixF sc
        (\recVar i2Var -> do
            n9 <- scNat sc 9
            boolTy <- scBoolType sc
            n32 <- scNat sc 32
            elemTy <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
            scGlobalApply sc "Prelude.at" [n9, elemTy, recVar, i2Var])
        (shiftMinusOne sc)
      classifyFixShape vecTy body @?= FixClassF

  , testCase "two-step lookback (subNat i 2) is Unrecognized" $ do
      -- Amendment C pins the CONSTANT -1 shift; a -2 lookback is out
      -- of the recognized class until a lowering for it is designed.
      (vecTy, body) <- mkFusedFixF sc
        (\recVar i2Var -> do
            n9 <- scNat sc 9
            boolTy <- scBoolType sc
            n32 <- scNat sc 32
            elemTy <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
            scGlobalApply sc "Prelude.at" [n9, elemTy, recVar, i2Var])
        (\iVar -> do
            n2 <- scNat sc 2
            scGlobalApply sc "Prelude.subNat" [iVar, n2])
      assertUnrecognized "two-step lookback" (classifyFixShape vecTy body)

  , testCase "same-index tail selection (no -1 shift) is Unrecognized" $ do
      -- Amendment C's syntactic side: result[i] reading the recursive
      -- vector at index i (instead of i-1) must NOT classify — it is
      -- exactly the unsound self-reference the audits rejected.
      (vecTy, body) <- mkFusedFixF sc
        (\recVar i2Var -> do
            n9 <- scNat sc 9
            boolTy <- scBoolType sc
            n32 <- scNat sc 32
            elemTy <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
            scGlobalApply sc "Prelude.at" [n9, elemTy, recVar, i2Var])
        pure
      assertUnrecognized "same-index tail" (classifyFixShape vecTy body)

  , testCase "bare rec as a zip operand is Class F" $ do
      (vecTy, body) <- mkFusedFixF sc
        (\recVar i2Var -> do
            n9 <- scNat sc 9
            n8 <- scNat sc 8
            boolTy <- scBoolType sc
            n32 <- scNat sc 32
            elemTy <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
            unitTy <- scGlobalApply sc "Prelude.UnitType" []
            sndTy  <- scGlobalApply sc "Prelude.PairType" [elemTy, unitTy]
            xsName <- scFreshVarName sc "xsz"
            xsVec  <- scGlobalApply sc "Prelude.Vec" [n8, elemTy]
            _xsVar <- scVariable sc xsName xsVec
            -- zip needs a second vector; a rec-free one — reuse a
            -- replicate-like gen over the seed element
            n0     <- scNat sc 0
            bv0    <- scGlobalApply sc "Prelude.bvNat" [n32, n0]
            jName  <- scFreshVarName sc "j"
            natTy  <- scNatType sc
            constF <- scLambda sc jName natTy bv0
            othVec <- scGlobalApply sc "Prelude.gen" [n8, elemTy, constF]
            zipped <- scGlobalApply sc "Prelude.zip"
                        [elemTy, elemTy, n9, n8, recVar, othVec]
            pairTy <- scGlobalApply sc "Prelude.PairType" [elemTy, sndTy]
            sel    <- scGlobalApply sc "Prelude.at"
                        [n8, pairTy, zipped, i2Var]
            scGlobalApply sc "Prelude.Pair_fst" [elemTy, sndTy, sel])
        (shiftMinusOne sc)
      classifyFixShape vecTy body @?= FixClassF

  , testCase "wrapped rec inside a zip operand is Unrecognized" $ do
      -- Sixth-audit Finding 0: the zip blessing must not extend
      -- below a bare rec operand — an index-permuting (or
      -- forcing-opaque) wrapper inside the zip slot is the same
      -- silent class as on the at-spine.
      (vecTy, body) <- mkFusedFixF sc
        (\recVar i2Var -> do
            n9 <- scNat sc 9
            n8 <- scNat sc 8
            boolTy <- scBoolType sc
            n32 <- scNat sc 32
            elemTy <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
            unitTy <- scGlobalApply sc "Prelude.UnitType" []
            sndTy  <- scGlobalApply sc "Prelude.PairType" [elemTy, unitTy]
            n0     <- scNat sc 0
            bv0    <- scGlobalApply sc "Prelude.bvNat" [n32, n0]
            jName  <- scFreshVarName sc "j"
            natTy  <- scNatType sc
            constF <- scLambda sc jName natTy bv0
            othVec <- scGlobalApply sc "Prelude.gen" [n8, elemTy, constF]
            revRec <- scGlobalApply sc "Prelude.reverse"
                        [n9, elemTy, recVar]
            zipped <- scGlobalApply sc "Prelude.zip"
                        [elemTy, elemTy, n9, n8, revRec, othVec]
            pairTy <- scGlobalApply sc "Prelude.PairType" [elemTy, sndTy]
            sel    <- scGlobalApply sc "Prelude.at"
                        [n8, pairTy, zipped, i2Var]
            scGlobalApply sc "Prelude.Pair_fst" [elemTy, sndTy, sel])
        (shiftMinusOne sc)
      assertUnrecognized "wrapped rec in zip slot"
        (classifyFixShape vecTy body)

  , testCase "index-permuting wrapper on the rec spine is Unrecognized" $ do
      -- @at (reverse rec) i2@ selects with the lookback direction
      -- FLIPPED — blessing the whole rec-containing spine as a zip
      -- slot would classify it, so the scan admits only the bare
      -- recursive vector or zip slots under an at-selection.
      (vecTy, body) <- mkFusedFixF sc
        (\recVar i2Var -> do
            n9 <- scNat sc 9
            boolTy <- scBoolType sc
            n32 <- scNat sc 32
            elemTy <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
            revRec <- scGlobalApply sc "Prelude.reverse" [n9, elemTy, recVar]
            scGlobalApply sc "Prelude.at" [n9, elemTy, revRec, i2Var])
        (shiftMinusOne sc)
      assertUnrecognized "reversed rec spine" (classifyFixShape vecTy body)

  , testCase "rec use outside zip/at slots is Unrecognized" $ do
      -- atWithDefault reads the same element as at, but it is not in
      -- the recognized selector family — reject-when-unsure.
      (vecTy, body) <- mkFusedFixF sc
        (\recVar i2Var -> do
            n9 <- scNat sc 9
            boolTy <- scBoolType sc
            n32 <- scNat sc 32
            n0 <- scNat sc 0
            elemTy <- scGlobalApply sc "Prelude.Vec" [n32, boolTy]
            dflt <- scGlobalApply sc "Prelude.bvNat" [n32, n0]
            scGlobalApply sc "Prelude.atWithDefault"
              [n9, elemTy, dflt, recVar, i2Var])
        (shiftMinusOne sc)
      assertUnrecognized "atWithDefault rec use" (classifyFixShape vecTy body)

  , testCase "rec-free element function is Unrecognized (not a recurrence)" $ do
      (vecTy, body) <- mkFusedFixF sc
        (\_recVar _i2Var -> do
            n32 <- scNat sc 32
            n0  <- scNat sc 0
            scGlobalApply sc "Prelude.bvNat" [n32, n0])
        (shiftMinusOne sc)
      assertUnrecognized "rec-free element" (classifyFixShape vecTy body)
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
    , antiRegressionLintTests
    , fixClassifierTests sc
    ]
