# Position-Directed Translation: Execution Plan

Date: 2026-07-08

## Purpose

Make the position/callee calculus
(`doc/2026-07-02_position-callee-calculus.md`) the *implementation* of the
SAWCore→Lean term translator, not a document the translator approximates.

Today the translator is **bottom-up**: it translates a term into its "natural"
shape and then repairs the shape locally using syntactic predicates
(`shouldWrapBinder`, `isVariableHead`, `natValueResult`, `typeArgPositions`,
`skipBinderWrap`, `inRecursorCaseBinder`) and, in a few places, by inspecting
the *emitted Lean AST* (`bindingShapeOfTerm`). The calculus is **top-down**:
the expected position `ρ` is pushed down from context, and a term's
representation is a function of `(ρ, source term)`.

The core judgment we must implement:

```
Γ ⊢ e : τ  ⟹_ρ  L : R(ρ, τ)
```

This plan turns that judgment into the actual signature of the recursion, one
reviewable slice at a time, keeping the suite green throughout.

## Why this is the right technical focus

- The proof-discharge command (`offline_lean` marking goals solved without
  invoking Lean) is deferred deliberately. It is bounded plumbing — the test
  harness already implements every check the product needs (exact goal type,
  `#print axioms` minus `sorryAx`, axiom allowlist) — and it can be done at the
  end without risk. It is **not** the deep problem.
- Emission correctness **is** the deep problem, and it is currently defended by
  "Lean's typechecker will reject a wrong shape" rather than "the calculus
  guarantees the shape". That is sound for shape mistakes (a raw/wrapped
  mismatch is a type error) but **not** for the cases where both
  representations typecheck: equality subject representation, recursor
  constructor order, and proof transport. Those are silent-unsoundness
  surfaces, and they are exactly the ones the bottom-up heuristics cannot
  reason about.

## Current state (verified against the code, 2026-07-08)

Entry points and recursion (`src/SAWCoreLean/Term.hs`):

- `translateTerm :: Term -> m Lean.Term` (4156) = `ttLean <$>
  translateTermWithShape`.
- `translateTermWithShape :: Term -> m TranslatedTerm` (4159) — **no position
  parameter**. This is the function the calculus says should be
  `translateAt :: ExpectedPosition -> Term -> m TranslatedTerm`.
- `translateTermUnshared` (4177) dispatches on `TermF`: `FTermF`, `Pi`,
  `Lambda`, application, constants, recursors.
- Application dispatch: `translateIdentWithArgsWithShape` (2710) →
  `originalDispatchWithShape` (2829), a ~380-line function that is the real
  callee dispatch. `calleeConventionForIdent` (2546) exists but resolves almost
  everything to `CalleeTransitional "classified by existing dispatch branch"`.

The calculus vocabulary already exists as data types (Term.hs:106–162) but is
barely threaded:

- `RawReason`, `ExpectedPosition`, `EqualitySubjectRep`, `RawLogicalCallee`,
  `CalleeConvention`, `RecursorConvention` are declared.
- `ExpectedPosition` is referenced in only ~4 places.
- `TranslatedTerm` (164) carries only `BindingShape` ∈
  {`BindingRaw`,`BindingWrapped`,`BindingFunction`} — **not** the full binding
  record the calculus's `Γ` requires (`source type, Lean name, expected
  position, representation, exact Lean type`).

The heuristics the calculus wants demoted, with current call-site counts:

| predicate | sites | role |
| --- | --- | --- |
| `skipBinderWrap` (reader flag) | 32 | suppress binder wrap for motives/indices |
| `shouldWrapBinder` | 29 | "is this type a value type?" by syntax |
| `typeArgPositions` / `Binders` | 18 | which binders are indices |
| `inRecursorCaseBinder` (reader flag) | 16 | keep recursor case binders raw |
| `isVariableHead` | 15 | assume var-headed type is a value |
| `natValueResult` | 9 | repair Nat result positions |
| `phaseBetaResultShape` | 8 | post-hoc result shape |
| `bindingShapeOfTerm` (AST inspection) | 14 | **forbidden**: guess shape from emitted Lean |

`bindingShapeOfLeanTermM` (falls back to `bindingShapeOfTerm`) is the one place
that directly violates the calculus's "no generated-Lean AST inspection" rule.
It is the highest-value single deletion target: once shape is an *output* of
`translateAt`, no site should ever re-infer it from syntax.

Recent commits (context): the live line of work has been promoting rows through
declarative contract tables — `55e4fe099 add position callee conventions`
(+397, the raw-logical `Eq`/`Refl`/`Eq.rec` slice), `429452873 promote fold
function conventions`, `27d749fb1 proof-carrying partial access wrappers`,
`d16870367 tighten checked-access prefix coverage`. The raw-logical slice
(Term.hs:2626–2677, `lowerRawLogicalCallee`) is the **one place the new
convention already drives translation top-down**, and it is the template to
generalize.

## The target architecture

```haskell
-- The core judgment. Position is an INPUT; shape is guaranteed by it.
translateAt :: ExpectedPosition -> Term -> m TranslatedTerm

-- Adaptation happens exactly once, at the boundary, and only via the
-- allowed-adapter relation. It NEVER inspects Lean syntax.
adaptTo :: ExpectedPosition -> TranslatedTerm -> m TranslatedTerm
```

`Γ` (the reader's binding environment) grows from `Map Lean.Ident BindingShape`
to carry, per binding: source type, Lean ident, the position it was bound at,
its representation, and its exact Lean type. This is what lets equality/proof
transport be sound without guessing.

Invariants we are buying:

1. Every emitted subterm is produced under a known `ρ`.
2. `adaptTo` only ever applies an allowed adapter (`Pure.pure` raw→runtime;
   `Bind.bind` runtime→raw *inside an error-preserving continuation*; identity
   raw→raw and runtime→runtime; eta for functions; checked-helper for
   proof-carrying). Forbidden adapters are unrepresentable, not just avoided.
3. Shape is never re-derived from emitted Lean. `bindingShapeOfTerm` is deleted.
4. Ambiguity is loud: if no `ρ` classifies a case, `translateAt` throws a
   `TranslationError`, never falls through to a "natural" guess.

## Guardrails (do not violate)

- No new Lean axioms; no `sorry` accepted as evidence; no `bv_decide`/
  `native_decide`.
- Do not classify by fixture name or emitted Lean AST.
- Do not use `DefPreserveRaw` (def-site) as a proxy for use-site convention.
- When a slice cannot classify a case, **reject and pin a fixture** rather than
  widening a heuristic.
- Break cleanly rather than preserving old behavior behind a flag. The only
  transitional artifact permitted is `CalleeTransitional`/an
  `ExpectPositionUnknown`-style bridge that is *tracked and shrinking*, never a
  permanent fallback.

## Validation commands (bounded — never run the full crypto suite unbounded)

All from `otherTests/saw-core-lean` with `SAW` pointing at the built binary
(`export SAW=$(find $(pwd)/../../dist-newstyle -name saw -type f -perm +111 | head -1)`).

- Build: `cabal build exe:saw` (from repo root) then `cabal test
  saw-core-lean-smoketest`.
- Focused single test (fast, the workhorse during a slice):
  `cd differential/<name> && bash ../../support/lean-differential-test.sh test`
  (analogously `lean-obligation-test.sh`, `lean-driver-test.sh`,
  `lean-proof-test.sh`).
- Conformance gate: `bash test.sh conformance` (differential + obligations +
  saw-boundary only; no crypto stress).
- Strict gate (no known gaps allowed to remain green):
  `bash test.sh conformance-strict`.
- `git diff --check` before every checkpoint.
- Lean support library: `cd lean && lake build`.

Do NOT run `bash test.sh test` (full sweep incl. crypto/LLVM stress) casually;
it is the source of the 100GB memory incident. Run focused rows + `conformance`
during development; reserve the full sweep for end-of-phase, and only if a
specific driver row is implicated.

Each slice below has an explicit **regression fence**: the exact rows that must
stay green (or improve) and the rows that prove the slice did something.

---

## Slice 0 — Instrument, don't change behavior (baseline + safety net)

Goal: make the current shape decisions *observable* so the migration can be
proven behavior-preserving row by row.

1. Add `ExpectedPosition` as the *documented* input to a new wrapper
   `translateAt ρ t`, initially implemented as: compute the shape the old code
   would have produced, assert it is consistent with `ρ`, then call the
   existing `translateTermWithShape`. No dispatch changes yet.
2. Add a debug env-var (e.g. `SAW_LEAN_TRACE_POSITIONS=1`) that logs
   `(ρ, term head, resulting shape)` at each `translateAt`. This is the
   differential oracle for the refactor: capture the trace on the current
   corpus, and after each later slice confirm the *emitted Lean is byte-identical*
   for all still-passing rows (the harness already deletes stale `.lean` and
   re-emits, so a golden-free diff of emitted artifacts is meaningful).
3. Snapshot current state: record which rows pass `conformance` and which
   known-gaps are pinned, so "green throughout" is checkable.

Regression fence: `cabal test saw-core-lean-smoketest` + `bash test.sh
conformance` unchanged. Emitted Lean unchanged (this slice is inert).

Deliverable: a `translateAt` seam that every subsequent slice narrows, plus a
reproducible before/after emitted-Lean diff procedure.

---

## Slice 1 — Enrich `Γ` and `TranslatedTerm` to the calculus record

Goal: stop collapsing raw-value / raw-index / raw-proof / raw-motive into one
`BindingRaw` bucket.

1. Extend the per-binding environment (`_bindingShapes` and friends in
   `TranslationReader`) from `Map Lean.Ident BindingShape` to a record carrying
   `{ sourceType, leanIdent, boundPosition :: ExpectedPosition, repr ::
   BindingShape, leanType :: Lean.Term }`. Keep a compatibility accessor that
   projects the old `BindingShape` so existing sites compile.
2. Extend `TranslatedTerm` to optionally carry the `ExpectedPosition` it was
   produced at (or a `RawReason` when raw). Keep `ttShape` as a projection.
3. At binder introduction sites (`translateBinder'`, `translateBindersSelective`,
   let-binding), record the real position instead of just wrapped/raw.

This slice changes data, not decisions. Emitted Lean must stay identical.

Regression fence: emitted-Lean byte-diff empty on all `conformance` rows;
smoketest green.

Deliverable: `Γ` is now precise enough that a raw proof variable and a raw
index variable are distinguishable — the precondition for Slices 4–5.

---

## Slice 2 — Make `adaptTo` the single adaptation chokepoint

Goal: one function performs all raw↔wrapped adaptation, and it is total over
the *allowed* adapters and rejects the forbidden ones.

1. Implement `adaptTo :: ExpectedPosition -> TranslatedTerm -> m TranslatedTerm`
   covering exactly the allowed adaptations from the calculus §Adaptation.
   Forbidden adaptations throw a new `TranslationError` variant
   (`ForbiddenAdaptation ρ shape`) — they must be impossible to emit.
2. Replace the scattered `translatedTermAsWrapped` (Term.hs:176, inserts
   `Pure.pure`) and `adaptWrappedFormal` (181) call sites with `adaptTo`. There
   are ~37 `translatedTermAsWrapped` uses; each becomes `adaptTo
   ExpectRuntimeValue`.
3. **Delete `bindingShapeOfTerm` / `bindingShapeOfLeanTermM`** (14 sites). Every
   consumer must instead read the shape from the `TranslatedTerm`/`Γ` record
   produced in Slices 1. This is the concrete elimination of emitted-AST
   inspection. If a site has no `TranslatedTerm` to read from, that reveals a
   missing position thread — fix it here or pin it.

Regression fence: emitted Lean identical on `conformance` rows *except* where
`bindingShapeOfTerm` was previously guessing wrong (those become either correct
or a loud rejection — inspect each diff; none may become *more* wrapped in a
proof/type position). Smoketest green.

Deliverable: adaptation is centralized and syntax-inspection is gone. This
alone closes the audit's "raw/wrapped inference from Lean AST" finding.

---

## Slice 3 — Push position through `Pi` / `Lambda` / `let`

Goal: replace the local rediscovery in the binder cases (Term.hs:4196–4235 and
the `translateFunctionWithWrappedResult`/`translateBindersSelective` machinery)
with position pushed down from the enclosing convention.

1. For `Lambda`: the expected position of the body is determined by the
   function convention of the surrounding position, not by re-running
   `isTypeProducing` + `shouldWrapBinder` + `natValueResult`. When we translate
   a lambda *at* `ExpectFunctionPosition c`, `c` tells us each binder's position
   and the result position directly.
2. For `Pi`: the return-type position comes from whether the Pi is itself in a
   type/sort position (already known from `ρ`), not from `shouldWrapBinder body`.
3. For shared `let`: choose the RHS position once, record the exact
   representation in `Γ` (Slice 1), translate the body against its own position.
   Implements calculus §Definitions "local let" rule. If one shared RHS is
   demanded at incompatible positions, emit separate bindings or reject — do not
   guess.
4. Demote `shouldWrapBinder`, `natValueResult`, `phaseBetaResultShape`,
   `isVariableHead` from *authorities* to, at most, helpers `adaptTo` may call
   when a convention explicitly asks "is τ a value type?" — never as the source
   of truth for position.

This is the largest behavioral slice. Do it **per binder-shape family** with a
focused fence, not all at once:

- 3a: value-level non-dependent lambdas (the `V(α)->V(β)` common case).
- 3b: dependent lambdas with index binders (the `bvAdd : (n:Nat)->...` case;
  `typeArgPositions` becomes the convention's declared index positions).
- 3c: motive lambdas (body type-level) — position `ExpectRaw RawMotivePosition`.
- 3d: `let` sharing.

Regression fence per sub-slice: the relevant `differential/*` families stay
green; specifically watch `differential/vector_fold`,
`differential/cryptol_ec_fold_scan` (higher-order value functions),
`differential/record_projection_binder`, and the `drivers/sequences` /
`drivers/offline_lean` rows that exercise dependent index binders. Emitted-Lean
diff reviewed, not just pass/fail.

Deliverable: `skipBinderWrap` and `inRecursorCaseBinder` reader flags become
derived from position rather than set imperatively; the binder cases no longer
call the syntactic value-type predicates as authorities.

---

## Slice 4 — Callee conventions: retire `CalleeTransitional`

Goal: `calleeConventionForIdent` returns a real convention for every callee, and
`originalDispatchWithShape` becomes a thin interpreter of conventions.

Restructured 2026-07-09 into sub-slices (4a–4c), after Slices 0–3 landed fully
byte-identical: the behavioral risk the plan spread across Slices 2–4 is
actually concentrated here, so Slice 4 takes the same sub-slice discipline as
Slice 3. Slice 4a is the first step whose fence is a *reviewed diff* rather
than an empty one — it fixes a live specimen.

### 4a — Checked-application conventions + the wrapped-index fix

1. Introduce the calculus's convention vocabulary as data
   (`ArgMode ::= TypeArg | IndexArg | RuntimeArg | RawValueArg | ProofArg |
   PropositionArg | MotiveArg | StructuralField | FunctionArg
   FunctionConvention`; `ResultMode ::= RuntimeResult | RawResult reason |
   FunctionResult FunctionConvention`) and re-express the
   `CheckedApplicationContract` arg tables in it — the `at`-family's
   `CheckedArgRaw` bucket splits into its true `IndexArg` (n, i) and
   `TypeArg` (a) slots.
2. The convention interpreter adapts each actual per its declared mode:
   `RuntimeArg` → `adaptTo ExpectRuntimeValue`; `IndexArg` with a *wrapped*
   actual → an error-preserving `Bind.bind` binding the index to a fresh raw
   variable consumed by BOTH the bounds proposition and the checked helper
   (sequenced in application order, calculus §Callee Conventions); `IndexArg`
   with a function actual and `TypeArg` with a wrapped actual → forbidden
   (loud). This fixes the live specimen `drivers/llvm_chacha20_core_verify`
   (today `CheckedArgRaw` passes a wrapped shared index raw into `LT.lt` and
   `atWithProof_checkedM`, which does not elaborate).
3. Pin fixtures: a small obligations row with a runtime-computed (wrapped)
   index into `at` (the specimen's minimal shape), so the fix is fenced by a
   fast row and not only by the heavyweight LLVM row.

Fence: emitted Lean byte-identical EXCEPT rows whose checked applications
previously received wrapped actuals at raw slots (those were ill-typed; each
diff reviewed). `llvm_chacha20_core_verify` goes green including elaboration;
the new fixture row is green; `obligations/vector_*_with_proof` and
`obligations/cryptol_ec_*` contracts unchanged.

### 4b — Phase-beta ordinary definitions + partial-op unification

1. The Phase-beta ordinary-definition path (the `funType`/`retTypeOfFun`
   lift-decision) becomes `CalleePhaseBetaDefinition` with argument positions
   read once from the callee's SAWCore Pi type: index binders →
   `IndexArg`/`TypeArg`, value binders → `RuntimeArg`, result →
   `RuntimeResult`/`RawResult`. Replaces the inline
   `typeArgPositions`/`shouldLift` logic.
2. Lift `PartialOpContract` / `ProofPrimitiveContract` / `UseMapsToWrapped`
   argument tables into the same `ArgMode` vocabulary (they already encode it
   informally; the partial-op bind plan becomes the interpreter's generic
   wrapped-at-raw-index rule).
3. `applyKnownFunctionWithShape` and the partial-application path adapt each
   supplied prefix arg through the convention (calculus §"For partial
   application"), never by binding all args to raw first. This is also where
   3b's dormant dependent-lambda conventions go live — pin a dependent
   higher-order fixture here.

### 4c — Retire `CalleeTransitional`; decompose the dispatch

`calleeConventionForIdent` returns a real convention for every callee;
`originalDispatchWithShape` becomes a thin interpreter over the convention
table. Shrink `CalleeTransitional` to zero — track the count per commit; it
only goes down.

2026-07-10 survey (post-4b): `translateIdentWithArgsWithShape` is already a
declarative guard chain (contract tables + name/arity patterns → explicit
lowerers; fallback = the UseSiteTreatment interpreter + the now
convention-driven phase-beta path). Step order for the remaining semantic
content:

1. **`applyKnownFunctionWithShape` peel demotion — own oracle cycle.** A
   DIFFERENT convention family from `applied`'s raw-formal targets: these
   callees are phase-β function VALUES whose emitted formals are wrapped, so
   value formals expect wrapped actuals (`expectedWrapped` = peeled
   `isExceptStringType`). Derivation candidate: expectedWrapped ⟺ mode
   `RawValueArg` — EXCEPT dependent/var-headed formals, where the peel sees
   the un-substituted Lean variable (never Except-headed → False) while a
   naive source classification says value formal (True). The candidate must
   map var-headed formals without a Pi instantiation to raw (peel-mirror);
   the inert assert adjudicates, same pattern as 4b steps 2–3.
2. **Proof-primitive table relabel** with SAWCore signatures in hand (raw
   slots are raw-LOGICAL `withRawTranslationMode` translations; the relabel
   documents Index/Type/Value/Proof slots without changing interpretation).
3. **`UseMapsToWrapped` arg table → `ArgMode`** (`UseArgRaw` splits into its
   true Index/Type slots, as 4a did for the checked contracts).
4. **Classifier-as-data + `CalleeTransitional` → 0**: fold the guard chain
   into a payload-carrying classified-callee type (note:
   `ProofPrimitiveContract` has rank-2 fields, so the classified type cannot
   derive Eq/Show), then delete `CalleeTransitional` and add the Slice 7
   anti-regression lint hook.
5. **`bindingShapeOfType` demotion** at binder sites — the remaining type
   self-mirror; the position that CHOSE the binder type (recorded since
   Slices 3a–3c) becomes the authority.

Regression fence (all sub-slices): `bash test.sh conformance` — differential +
obligations + saw-boundary all at prior status or better. The proof-carrying
obligation rows (`obligations/partial_*`, `obligations/cryptol_ec_*`,
`obligations/vector_*_with_proof`) must keep emitting identical contracts.

Deliverable: application is table-driven by conventions with explicit modes;
the 380-line `originalDispatchWithShape` is decomposed into a convention
interpreter + the convention table.

---

## Slice 5 — Equality subject representation & proof transport (the deep, silent-risk core)

Goal: generalize the working raw-logical slice (`lowerRawLogicalCallee`,
Term.hs:2626–2677) into the full §"Raw Logical Callees" convention, so equality
carrier and proof transport are *declared*, never inferred from type names.

This is where getting it wrong is a **silent** soundness bug (both `Nat` and
`Except String Nat` carriers can typecheck), so it depends on Slices 1–4 being
in place (precise `Γ`, centralized `adaptTo`, real conventions).

**Status update (2026-07-10, entering the slice):** the six load-bearing rows
listed below (`proof_add_nat_assoc`, `proof_eq_nat_add_0/_s/_comm`,
`proof_equal_nat_to_eq_nat`, `proof_transport_runtime_subject`) are ALREADY
green positives — the working raw-logical slice fixed them before this plan's
Slice 5 began. They are therefore this slice's **regression fence**, not its
target. The remaining work is architectural: the subject representation is
still *inferred bottom-up* (`subjectRepFromTranslatedOperands` inspects
translated operand shapes) rather than *declared* by the surrounding
convention, the `Eq.rec` convention records none of the calculus's required
field set (it demands all-raw and rejects everything else), and the
function-carrier decision is unmade (blanket rejection; keeps
`drivers/sawcore_prelude_auto_emit` red). Corpus survey of the 626-file
baseline confirms the calculus's warning empirically: `Bool` and `Nat`
carriers appear both raw (`@Eq Nat`, `@Eq.{1} Bool Bool.true`) and runtime
(`@Eq.{1} (Except String Bool …)`, `@Eq (Except String Int …)`) — the carrier
type name cannot decide ρ_eq; the operand domain does.

Sub-slices (mirroring the Slice 4 restructure):

### 5a — declared subject representation; kill the universal bottom-up authority

1. `equalityPropositionAtSubjectRep` becomes the single entry point for every
   surround that KNOWS its ρ_eq (today: `unsafeAssert`, declared raw — its
   fixtures pin raw `@Eq.{2} Type` / `@Eq.{1} Nat` carriers). No such surface
   may fall through to re-inference.
2. The standalone-proposition convention (top-level `Eq`/`Refl`/`Eq__rec`
   reached through ident/recursor dispatch with no equality-aware surround) is
   DEFINED and documented: ρ_eq := the joint produced domain of the source
   operands under the current translation mode — `RuntimeValue` iff any
   operand's declared production record (`ttShape`, stamped by producers since
   Slice 1/2, never read off emitted Lean AST) is wrapped, raw otherwise,
   function-carrier rejected until 5c. This is byte-for-byte the legacy
   result, so 5a is a byte-parity slice; what changes is its STATUS — from
   universal inference to one convention among several, bypassed wherever a
   surround declares ρ_eq — and its auditability (subject-rep decisions traced
   under `SAW_LEAN_TRACE_POSITIONS`). Rename
   `subjectRepFromTranslatedOperands` → `standaloneEqualitySubjectRep` with
   the convention contract in its doc comment.
3. Operands then translate/adapt AT the declared position through the
   `adaptTo` chokepoint (as today: raw→runtime via `Pure.pure` only; a
   runtime operand demanded raw is `ForbiddenAdaptation`, never unwrapped).

Fence: byte-identical emissions vs the slice0 baseline; smoketest;
conformance exit 0.

### 5b — the full `Eq.rec` field set

1. Record the calculus's required fields in an `EqRecConvention`: operand
   position ρ_eq, carrier `SubjectRep(a, ρ_eq)`, motive binder positions,
   motive result position (reuse `MotiveConvention` from 3c), branch position,
   proof position, final result position, universe class. `Γ` (Slice 1)
   preserves the exact proposition/proof Lean type for proof variables.
2. The point of the field set is **consistency by construction**: the motive's
   inner `Eq` occurrence, the branch, and the transported proof all receive
   the SAME declared ρ_eq. Today that consistency holds only by mode
   coincidence (motives translate raw-mode, so inner-Eq inference happens to
   agree with the all-raw operand demand) — which is exactly why
   runtime-subject transports are currently rejected wholesale.
3. Generalize the lowering beyond all-raw: a standalone `Eq__rec` whose
   declared ρ_eq is `RuntimeValue` (wrapped operands) becomes expressible,
   with motive binder `y : Except String T`, inner proposition over the
   wrapped carrier, and branch position derived from the motive result mode.
   Add a fixture row pinning one such transport. Surfaces the declared-rep
   reconciliation question (e.g. an `unsafeAssert`-produced proof feeding a
   runtime-subject `Eq__rec` must agree on the carrier — reject on mismatch,
   never coerce).
4. Function-carrier operands stay rejected (5c). If the fields cannot be
   determined uniquely, reject; never guess.

Fence: the six load-bearing rows stay green; no wrapped-value equality row
regresses to raw (guard: an `Eq` over a `bvToNat`-style runtime computation
still compares `Except String Nat`); new-capability rows via exact obligations
and `lean_verify`/`#print axioms` axiom-cleanliness; NOT byte-parity (new
emissions), reviewed diff instead.

### 5c — the function-carrier equality decision

Function-carrier equality (currently a blanket rejection) gets its convention
decided deliberately: the leading candidate is raw `@Eq` over the *translated
effectful* function type (`V(α) → V(β)`, i.e. `T(α) → Except String (T(β))`),
which compares the functions SAW actually denotes — never a rawified
value-level signature invented to make a row pass. Expected to fix the
pre-existing red `drivers/sawcore_prelude_auto_emit` (a prelude lemma's
function-carrier equality rejects since `55e4fe099`). Promote
`obligations/proof_coerce_eq`, `proof_bv_eq_to_eq_nat`, `proof_prove_le_nat`,
`proof_nat_compare_le` only via exact obligations or axiom-clean theorems —
these are optional promotions, not slice-blocking.

Fence: `sawcore_prelude_auto_emit` green with reviewed diff and Lean
elaboration; conformance exit 0; the six rows stay green.

Deliverable: proof transport is sound by construction from the declared subject
representation — every equality-emitting surface either declares ρ_eq or is the
documented standalone convention; `Eq.rec` carries the full field set; the
function-carrier question is decided, not deferred by rejection. (The
`proof_add_nat_assoc`-class failures closed before this slice; the slice makes
their fix principled and keeps them closed.)

---

## Slice 6 — Recursors as a position/callee instance + constructor-order safety

Goal: fold `RecursorConvention` into the shared model and close the
`@Foo.rec`-by-name constructor-order trust hole (Term.hs:4101).

1. Recursor result classification (`classifyRecursorResult`/`recursorConvention`,
   3641–3672) reads the motive result *position* from the shared machinery
   instead of local predicates: `RecursorReturnsWrappedValue` iff the motive
   result position is `ExpectRuntimeValue`, etc.
2. Constructor-order safety: for every inductive whose `@Foo.rec` we emit with
   SAW's positional argument order (Either, Stream, PairType, RecordType, and
   any user datatype), either (a) emit an assertion Lean checks that the Lean
   inductive's constructor order matches SAW's, or (b) route through a
   source-shaped support recursor (the Case B mechanism from
   `doc/2026-07-03_direct-recursor-semantics-design.md`). The six currently
   gated families (`Nat/Pos/Z/Bool/AccessibleNat/AccessiblePos`) stay rejected.
   This removes the only *silent* (typechecks-but-wrong) recursor risk.

This slice is the natural bridge to the direct-recursor / `PosRep` work
(`doc/2026-07-03_direct-recursor-semantics-design.md`), which becomes tractable
once recursors are position-driven. That larger work (raw `Nat#rec`, `PosRep`
inductive, user-datatype auto-emission) is **out of scope for this plan** and
tracked separately; it should start only after Slices 0–6 land.

Regression fence: `differential/unit_recursor_raw_scrutinee`,
`differential/cryptol_vector_eq_dictionary`,
`recursor_wrapped_scrutinee_error_propagates`,
`recursor_wrapped_scrutinee_function_result_error_propagates`,
`drivers/cryptol_module_simple`, `drivers/cryptol_polymorphic_class_dict` stay
green. `saw-boundary/{natrec,boolrec,zrec_rejection,...}` still reject.

Deliverable: recursors use the shared position model; no inductive is emitted
with unchecked constructor-order trust.

---

## Slice 7 — Delete the demoted heuristics; docs & invariants

Goal: make the migration irreversible and auditable.

1. Delete or reduce to documented one-line helpers: `phaseBetaResultShape`,
   `natValueResult`, and the standalone authority uses of `shouldWrapBinder` /
   `isVariableHead`. Any survivor must have a comment stating it is a
   convention-internal predicate, not a position authority, with the convention
   that calls it.
2. Confirm `bindingShapeOfTerm` and all emitted-AST inspection are gone (grep
   gate in a test or CI check).
3. Update `STATUS.md`, `TODO.md` Priority 2 items ("promote design from
   scattered policy to explicit data types", "centralize adaptation", "replace
   transitional local policy") to reflect completion, and update the calculus
   doc's "Current Rough Edges" section.
4. Add an anti-regression check: a source-level lint that fails if
   `bindingShapeOfTerm`, a `CalleeTransitional`, or a new emitted-AST shape
   inspection reappears.

Regression fence: full `bash test.sh conformance-strict` at prior-or-better
status; `cabal test saw-core-lean-smoketest`; `lean/ lake build`.

Deliverable: the calculus *is* the implementation; the transitional heuristics
are gone or explicitly subordinate.

---

## Sequencing, risk, and stop conditions

Order: **0 → 1 → 2 → 3 → 4 → 5 → 6 → 7.** Slices 1–2 are data/plumbing and must
be emitted-Lean-inert (strong safety). Slice 3 is the largest behavioral change
(do it in 3a–3d sub-steps). Slice 5 is the deepest correctness payoff and
depends on 1–4. Slice 6 sets up the separately-tracked direct-recursor work.

**Reorder (2026-07-10, post-Slice-5 design review, with user):** the
emission-quality debts slice (TODO §Deliberate emission-quality debts:
bind-iff-wrapped `RawValueArg`; instantiation-directed var-headed modes) runs
**between 5 and 6**. Rationale: the debts are the source of the false
raw-mode production records that already forced two mode-guard workarounds in
Slice 5; Slice 6.1's recursor classification consumes those same records and
must get truthful inputs rather than a third guard; and the declared equality
subject rule is semantically justified by records being the translator's
single source of truth. Slice 6's constructor-order hole guards against
future drift (current families match Lean's order and carry behavioral
differential rows), so it tolerates the delay.

**Debts slice COMPLETE (2026-07-10; TODO §Deliberate emission-quality debts
carries the full record).** All three predictions of the reorder rationale
held. Notably, the false-record mechanism turned out to be a third site (the
raw-mode application paths stamped `phaseBetaResultShape` over raw
emissions), and once `rawModeResultShape` made raw-mode records truthful,
BOTH Slice 5 mode-guards collapsed into the single mode-uniform
`lowerRawLogicalCallee` pipeline byte-identically across the corpus —
including the auto-emitted raw prelude. `equalityPropositionAtSubjectRep`
(the declared-rep entry point) went with them: no surround declares a ρ_eq
anymore; every equality surround classifies from production records. Slice 6
starts from truthful records and zero mode-guards.

**Slice 6 COMPLETE (2026-07-10, commits `2000c7719` + `133f2cd69`; TODO
carries the full record).** 6.1 landed emission-inert (corpus
byte-identical): the recursor convention derives from a declared
`recursorMotiveResultPosition` — the shared domain analysis plus two
declared refinements (non-Prop Nat elimination computes a runtime value;
var-headed type families stay raw) — and a function motive carries a full
`FunctionConvention` whose result position mirrors the Pi translator's
body-wrap rule; `classifyRecursorResult` and the recursor's
`phaseBetaResultShape` call are gone. 6.2 chose mechanism (a),
generated-at-emission assertions, over source-shaped support recursors:
option (b) leaves same-payload constructors silently swappable under
constant motives when the *SAWCore* side reorders, while the emitted
`saw_ctor_order` command (support library `SAWCoreCtorOrder.lean`, with
positive and `#guard_msgs`-negative self-tests at every lake build)
carries SAWCore's declared order into the file and catches both drift
directions. Assertion names are fully qualified — command-level
resolution has no expected type to disambiguate core-colliding short
names (`Stream`, `Either`). `Eq.rec` is out of scope by design (declared
`EqRecConvention` onto Lean-core `Eq`, single constructor, no
support-library inductive to drift). The six gated families stay
rejected. Slice 7 starts with the recursor family fully on the shared
model and zero unchecked constructor-order trust.

**Slice 7 COMPLETE (2026-07-11) — THE PLAN IS DONE.** The value-domain
result rule centralized in `phaseBetaResultIsValue` (seven restatements
of the `shouldWrapBinder || isVariableHead || natValueResult`
disjunction collapsed byte-identically); `natValueResult` and
`phaseBetaResultShape` demoted to documented convention-internal
helpers; the smoketest gained the anti-regression source lint
(forbidden-name check over the ten deleted heuristics, validated to
fire; ceiling gates on the two allow-listed emitted-TYPE self-mirrors).
`STATUS.md`, the TODO Priority 2 items, and the calculus doc's new
"Implementation Status" section record the end state. One deliberate
non-goal: the `applyKnownFunctionWithShape` result peel keeps its
self-mirror — the source-derived swap can diverge under
`inRecursorCaseBinder`-suppressed type wraps and needs its own
inert-oracle step; the lint caps it instead. Definition of done:
`translateAt` is the core recursion, `adaptTo` the only adaptation
site, forbidden adaptations unrepresentable, emitted-AST inspection
deleted and lint-gated.

Each slice is one or a few commits, each with: `git diff --check`, `cabal build
exe:saw`, `cabal test saw-core-lean-smoketest`, `bash test.sh conformance`, and
a reviewed emitted-Lean diff on the slice's regression fence. Commit only on a
green fence — no micro-commits, no progress-note commits.

Stop and redesign (per calculus §Stop Conditions) if a slice wants to: classify
by fixture name or emitted Lean syntax; use `DefPreserveRaw` as a hidden
use-site proxy; rawify functions/proofs/motives to make a row pass; or accept a
`sorry` obligation as evidence. In those cases, pin a fixture and reject rather
than widen a heuristic.

## What this plan explicitly does NOT do

- It does not build SAW-side Lean replay (`offline_lean` discharge). Deferred by
  design; bounded end-game plumbing.
- It does not implement direct `Nat#rec`/`Pos#rec`/user-datatype recursors or
  the `PosRep` inductive. Slice 6 makes that tractable; the work itself is
  tracked by `doc/2026-07-03_direct-recursor-semantics-design.md`.
- It does not add Lean proof automation or discharge BV-heavy crypto. Emission
  correctness only.
- It does not prove the two Vec↔BitVec round-trip axioms (separate, cheap TCB
  task).

## Definition of done

- `translateAt :: ExpectedPosition -> Term -> m TranslatedTerm` is the core
  recursion; position is an input everywhere.
- `adaptTo` is the only adaptation site; forbidden adaptations are
  unrepresentable; `bindingShapeOfTerm`/emitted-AST inspection deleted.
- `calleeConventionForIdent` returns a real convention for every callee;
  `CalleeTransitional` count is zero.
- Equality subject representation and `Eq.rec` transport are declared, and the
  five Nat proof-transport rows + runtime-subject row are positive, axiom-clean.
- No inductive is emitted with unchecked constructor-order trust.
- `bash test.sh conformance-strict` and `cabal test saw-core-lean-smoketest`
  green; `lean/ lake build` green; emitted-Lean diffs reviewed at each slice.
