# Under-applied partial-op function wrappers (W1: the intDiv blocker)

2026-07-18. Status: AUDITED — SAFE-WITH-CONDITIONS (verdict + five binding conditions at end; the Nat-family total-lift hypothesis was REFUTED and is struck below). Unblocks rev.cry whole-module
translation (PIntegral dictionary fields carry partial ops
UNAPPLIED; pinned by saw-boundary/polymorphic_seq_module_rejection).

## Problem

Partial-op contracts (Contracts.hs) lower APPLIED occurrences at
exactly contract arity, wiring per-application checked evidence
(h_nonzero). A partial op in FUNCTION-VALUE position (dictionary
field `div = intDiv`; partial application) has no application site
to attach evidence to, and an eta-expanded obligation over the
lambda-bound divisor would be universally quantified — unprovable
(the OP-3 lesson: never emit obligations where they cannot be
proved). Today: named rejection.

## Semantics ground truth (the zero points)

- `intDiv`/`intMod`: SAW concrete simulator = Haskell div/mod
  (Concrete.hs:213 `bpIntDiv = pure2 div`) — divisor 0 CRASHES
  (⊥). Lean support `intDiv := Int.fdiv` is TOTAL (x/0 = 0). The
  zero points DIVERGE; equating them unguarded would be silent
  0-vs-⊥ unsoundness. The checked contract's `Not (y = pure 0)`
  hypothesis exists precisely to exclude this point.
- `divNat`/`modNat`/`divModNat`: hypothesis REFUTED by audit. The
  simulator does NOT run the Prelude recursion; it uses native
  `divModNatOp` = Haskell `divMod` (Prims.hs:718-724) — concrete
  zero point CRASHES; symbolic routes to bvUDiv = SMT all-ones.
  Three-way divergence with Lean's total Nat.div. THROW like every
  other op.
- bv division family: zero-point semantics were pinned in the
  earlier zero-divisor work; per-op table entry required.

## Design: runtime-checked wrapper values (the OP-2 pattern lifted
to function position)

For each partial op the contract table gains an
`underAppliedWrapper` field naming a support-library RUNTIME
wrapper, e.g.

    def intDiv_runtimeM (x y : Except String Int) :
        Except String Int := do
      let x' <- x; let y' <- y
      if y' = 0 then throw "intDiv: division by zero"
      else pure (intDiv x' y')

Lowering rule: a contract-bearing partial op at LESS than contract
arity lowers to its wrapper (partially applied to the available
actuals under the wrapper's wrapped-formal convention —
phaseBetaFunctionValueModesFor family). Zero new recognizer
surface; the dispatch already knows the arity mismatch (the
current reject site). APPLIED sites keep the proof-carrying path
(evidence ⇒ provably error-free, raw-capable results).

Soundness: value semantics identical away from the zero point; AT
the zero point SAW is ⊥/crash and the wrapper is an Except error —
the calculus's standard error-effect mapping (fix_error_elem
precedent: escaping SAW runtime error vs Lean Except error =
agreeing outcome). For ops whose SAW zero point is DEFINED (Nat
family, if confirmed) the wrapper is the plain total lift and the
zero check is OMITTED — a per-op table decision, never a global
rule. [AUDIT RESULT: NO op qualifies — division-by-zero is
genuinely undefined in SAWCore (concrete crash, symbolic
unconstrained SMT value, mutually divergent), so an Except THROW is
the ONLY sound representation at every excluded point: a throw
never defeq-equals any `pure v`, so false equations cannot close —
divergence is always a failed proof, loud.]

## Audit questions (for the pre-implementation audit)

1. Per-op zero-point table: verify EVERY partial-op contract's SAW
   concrete/symbolic semantics at the excluded point (intDiv,
   intMod, divNat, modNat, divModNat, bvUDiv, bvURem, bvSDiv,
   bvSRem, Cryptol signed family) against the proposed wrapper.
   Symbolic backends (What4/SBV) may define division at 0 (SMT
   semantics: bvudiv x 0 = ones!) — if SAW's SYMBOLIC zero point
   differs from concrete, which is "SAW semantics"? (Likely
   resolution: the backend translates SAWCore's own semantics =
   the simulator's; document.)
2. Error-message policy: SAW concrete CRASHES (no message) — is a
   canonical wrapper message acceptable under the differential
   error-outcome contract (currently unimplemented comparison)?
3. Convention fit: the wrapper value's type must match what
   phaseBetaFunctionValueModesFor declares for a var-headed/known
   function slot at the use site (dictionary field positions).
4. Interaction with OVER-application (contract arity < spine):
   currently also rejected — same wrapper + residual application?
5. No new obligations anywhere (the design emits ZERO proof
   obligations for wrapped values) — confirm no path smuggles an
   eta-local h_nonzero back in.


## Audit verdict (2026-07-18): SAFE-WITH-CONDITIONS

Per-op zero-point table established from primary sources (see the
audit message record): intDiv/intMod concrete = Haskell div/mod
crash, symbolic = unconstrained SMT; Nat family = native divMod
crash / bvUDiv all-ones; bv family = Prim.divideByZero crash /
SMT all-ones (the Prelude.sawcore comments document only the
SYMBOLIC behavior — not concrete truth); rational family crashes.
UNIFORM CONCLUSION: every wrapper THROWS at the excluded point.

Binding conditions:
1. Nat-family wrappers throw (total-lift carve-out struck).
2. Wrapper nonzero branch defeq-identical to the matching
   *_checkedM body (same support op, same wrapped arg convention)
   — keeps the both-representations probe benign (away from zero
   both reduce to the same `pure`; at zero only the wrapper exists
   and a throw never closes an equation against a value).
3. Wrapper Lean type = the translated dictionary-field slot type:
   all-Except arrows, NO proof argument (why *_checkedM cannot be
   the field value); relies on the no-rawify-dictionaries rule.
4. Dispatch gates on STRICT under-application (nArgs < arity),
   placed after the exact-arity contract match — full-arity rows
   cannot change; over-application stays rejected
   (defense-in-depth; vacuous for non-function-result ops).
5. The wrapper path emits ZERO proof obligations — bypasses the
   proof-carrying builders entirely (plain Lean.App).

Non-issues: error-message content (throw is soundness-inert;
distinct per-op messages for hygiene), over-application,
both-representations conflation, concrete-vs-symbolic ("which is
SAW?" — neither is adoptable as a value; throw is the only
representation consistent with both).
## Extension (2026-07-18): total raw-target ops in dictionary fields

After the partial-op wrappers landed, rev.cry translation succeeds
and the frontier is TOTAL mapped primitives (intNeg in
PRingInteger) unapplied in dictionary fields: the field slot's
TYPE-side translation is the wrapped arrow (the Pi translator wraps
value-domain Pis), but the VALUE side delivers the raw-target var
"structurally" (FunctionArg Nothing from instantiationMode's Pi
arm) — a producer/consumer representation split inside one
emission, caught loudly by Lean (pinned:
differential/cryptol_rev_module).

Design (position-directed, two parts):
1. `instantiationMode`: a Pi instantiation derives its DECLARED
   convention from the instantiating Pi itself —
   `FunctionArg (Just conv)` via the standard Pi→convention
   derivation (the `recursorMotiveFunctionConvention` analysis,
   generalized/renamed `piFunctionConvention`) — instead of
   committing to Nothing. This makes the value side read the SAME
   authority the type side already uses.
2. Non-lambda actuals at a declared convention: the
   `ExpectFunctionPosition (Just conv)` consumers currently handle
   only Lambda heads; a Constant/var-headed function value whose
   produced formals mismatch the convention eta-adapts (the
   `translateFunctionToWrappedFormal` non-lambda pattern:
   translate as-produced, then convention binders + `buildLifted`).
   Adaptation stays convention-driven — no new adaptTo arm; the
   eta form is constructed at the position that declared the
   convention.

Soundness shape: pure representation adaptation of TOTAL functions
(no excluded points, no obligations); divergence impossible away
from representation (eta of a total raw op = pure-lift per
argument), and any mismatch remains a loud Lean type error. The
one care point: do NOT eta-adapt at RAW-target callee positions
(their formals are genuinely raw — the existing structural
delivery is correct there); the convention derivation only fires
where the instantiating Pi's translation wraps.

### Located implementation points (2026-07-18 grounding)

- Part 1: `instantiationMode` (Term.hs ~724), the
  `DFunction -> FunctionArg Nothing` arm; the Pi→convention
  derivation to reuse is `recursorMotiveFunctionConvention`
  (Term.hs ~1064) — generalize/rename `piFunctionConvention` (it
  is already generic over a Pi type; only the name is
  motive-specific).
- Part 2 consumers: the generic application path translates
  actuals to `argResults` BEFORE modes and never adapts supplied
  function actuals (Term.hs ~2747 eta region: modes drive only
  bind/splice and MISSING-formal eta). Supplied actuals at
  `FunctionArg (Just conv)` must translate at
  `ExpectFunctionPosition (Just conv)`; the position consumer for
  non-Lambda heads (Term.hs ~4687 guards on `Lambda{}`) extends
  with the `translateFunctionToWrappedFormal` non-lambda pattern
  (translate as-produced; if produced formals mismatch the
  declared convention, eta via convention binders + `buildLifted`).
- The checked-application interpreter's `FunctionArg` arm
  (Term.hs ~1823) already routes through
  `adaptTo (ExpectFunctionPosition mconv)` — it inherits part 2's
  consumer extension for free.
- Regression surface: `differential/cryptol_rev_module` flips when
  this lands (promote to true differential row + un-fail demo step
  3); raw-target callee rows (bvAdd-family drivers) must be
  bit-identical (their FunctionArg positions are raw-formal and
  must NOT gain eta).

### Part 3 (found by landing parts 1-2): call-site discipline

Parts 1-2 landed 2026-07-18 (instantiation-derived conventions;
`translateFunctionActualAtConvention` eta-adapts mapped raw-formal
globals at declared-convention slots). The rev-module frontier
moved to two residuals, both loud, pinned by
`differential/cryptol_rev_module`:

1. APPLYING a wrapped-formal function value (dictionary field,
   runtime wrapper) still uses the raw-formal call discipline —
   actuals are bound to raw then spliced (`intDiv_runtimeM v_0`
   with `v_0 : Int`). The application path for function VALUES
   must use the S5 family discipline (wrapped formals: supply
   wrapped actuals as-is) when the callee value carries wrapped
   formals — the callee-representation question the production
   record already answers (`BindingFunction` produced by the
   eta/wrapper paths is wrapped-formal; `applyKnownFunctionWithShape`
   currently re-derives raw-formal discipline from the SAW type).
2. `applied f [] = pure (TranslatedTerm f BindingRaw)` mis-stamps
   zero-arg function-typed mapped globals as raw DATA, so
   RuntimeArg slots legally pure-lift them (`pure natToInt`
   applied to an eta arg). The honest stamp for a Pi-typed
   zero-arg global is BindingFunction (the in-code comment already
   concedes this); RuntimeArg consumers then reject/route it
   through the function machinery instead of value-lifting.

### Part 3 findings (2026-07-18, after the raw-formal gate fix)

The part-2 eta initially double-adapted partial-op wrapper values
(raw-formal discipline over the already-wrapped-formal
intDiv_runtimeM) — fixed by the raw-formal GATE:
eta only for Preserve/Rename globals (translateIdentToIdent Just)
with NO partial-op contract; UseMacro/UseMapsToWrapped/wrapper
products pass through as-produced. intDiv/intMod errors gone.

Remaining (part 3b, pinned by differential/cryptol_rev_module —
all natToInt):
1. `applied f []` stamps zero-arg function-typed mapped globals
   BindingRaw; value slots then legally pure-lift them
   (`pure natToInt` applied to an eta arg). Honest stamp is
   BindingFunction for Pi-to-non-sort types; the consumer slots
   that today rely on the pure-lift must instead route through the
   declared-convention eta (or reject loudly).
2. A Num#rec function-ARGUMENT slot (`Nat -> Except String Int`
   motive-derived formal) receives raw `natToInt` — recursor
   argument positions need the same
   translateFunctionActualAtConvention treatment the generic path
   gained.
