# Either@core / Stream@core recursor-convention design (0.02 W1 final rung)

2026-07-17. Status: AUDITED — two independent audits complete
(SAFE-TO-IMPLEMENT WITH CONDITIONS); the operative design is the
KIND-DIRECTED rule + shared classifier below, superseding
candidate A's bare-vs-applied split. See the audit-verdict section
at the end and `2026-07-17_domain-map-coherence-audit.md`. Goal: `rev.cry` whole-module translation
(`write_lean_cryptol_module`) produces `Rev.lean`; the
saw-lean-example demo loses its `fails`-wrapped step 3.

## The failing shape (ground truth, traced 2026-07-17)

`implRev : {n, a} (fin n) => [n]a -> [n]a` lowers to

```
seqMap Integer a n' (\i -> ecAt n a Integer PIntegralInteger xs (…))
       (ecFromToLessThan 0 n Integer PLiteralInteger)
```

`ecAt` (finite arm) is `posNegCases ix pix a (at n a xs) (\_ -> …)`,
and `posNegCases a p r pos neg x = either Nat Nat r pos neg
(p.posneg x)`. Neither `posNegCases` nor `either` has a
SpecialTreatment mapping (only the `Either` TYPE maps), so the term
reaches the translator as a literal `Either#rec` application.

Traced classification at the reject:

- motive body = the BARE TYPE VARIABLE `a` (spine: `var`),
- `recursorMotiveResultPosition` classifies it
  `ExpectRaw RawValuePosition` via the `isVariableHeadTypeFamily`
  arm (a bare sort-0 variable counts as a zero-argument family),
- scrutinee `p.posneg x : Either Nat Nat` is a runtime value →
  wrapped,
- (Wrapped scrutinee, RawTypeOrProof result) →
  `rejectWrappedRawRecursor` — the pinned diagnostic in
  `saw-boundary/polymorphic_seq_module_rejection`.

## The asymmetry (why this looks like a rule gap, not new scope)

The calculus already answers "is a var-headed type a value domain?"
in FUNCTION-result position: `functionConventionResultIsValue`
(Term.hs) counts `isVariableHead ty` as a VALUE — function results
at var-headed types wrap (`Except String a`), and that rule shipped
through the position-directed audits. The recursor motive rule
(Slice 6.1) made the opposite, conservative call ("commit to
nothing and let Lean check the motive"). The Either@core hole is
exactly this asymmetry: one domain question, two answers.

## Proposed rule (candidate A — alignment)

In `recursorMotiveResultPosition`, classify a var-headed motive
body as `ExpectRuntimeValue` under the SAME conditions the
function-result rule commits to value-ness, instead of
unconditionally `ExpectRaw RawValuePosition`. Concretely: the
existing `isVariableHeadTypeFamily` arm splits —

- bare variable bound at `sort 0` / `isort 0` (zero-argument case):
  `ExpectRuntimeValue` — the recursor computes a value of type `a`,
  the motive wraps (`Except String a`), the wrapped-scrutinee
  `Bind.bind` path applies unchanged;
- APPLIED var-headed family (`p y pf` with `p : … -> Sort u`):
  stays `ExpectRaw` — the universe genuinely cannot be committed.

No new emission machinery: the change selects the EXISTING
`RecursorReturnsWrappedValue` path (Bind.bind sequencing, case
handlers translated with wrapped results) for a class that today
rejects. This matches the release plan's contract: new coverage =
new declared conventions, not translator re-architecture.

## Soundness analysis (for the audit to break)

1. **Value-domain instantiation** (`a := Vec/BitVec/tuple/...`):
   identical semantics to today's concrete value-type motives —
   the same Bind.bind path, same error propagation. Sound by the
   existing path's argument.
2. **`a := Num` (or another raw-by-representation type).** SAWCore
   `Num : sort 0` has data constructors, so `Num` CAN instantiate a
   sort-0 binder. Our representation keeps Nums raw
   (`isCryptolNumType`), so a wrapped-`a` polymorphic emission
   applied at `Num` mixes representations. Claim to verify: every
   such application site adapts through the `adaptTo` chokepoint
   against the emitted polymorphic type, so a mismatch surfaces as
   a Lean elaboration failure (LOUD), never a silent value change.
   The audit must probe this: construct a SAWCore term applying a
   wrapped-motive polymorphic recursor result at `Num` and at
   `Prop`-adjacent types, and check nothing elaborates to a wrong
   value.
3. **Prop instantiation.** SAWCore's `Prop` is `propSort`, distinct
   from `sort 0`; binders at `sort 0`/`isort 0` cannot be
   instantiated by propositions without a sort coercion the
   typechecker rejects. Verify against SAWCore's actual
   cumulativity rules (SAWCore.Term.Functor sort ordering) — if
   any cumulativity path allows Prop ≤ sort 0 instantiation, the
   rule must exclude it or the reject stays for that case.
4. **Scrutinee error semantics.** SAW's `either … (posneg x)` at an
   erroring `x` is ⊥/error; emitted `Bind.bind` propagates the
   `Except` error before entering the recursor — the strict
   semantics match (same argument as every existing wrapped
   recursor).
5. **Seam-bug pattern check.** All six prior seam bugs were
   syntactic rules UNDER-approximating forcing semantics. This
   change RELAXES a syntactic rule, so the failure mode to hunt is
   the dual: OVER-approximating value-ness (classifying something
   as wrappable whose SAW semantics demands rawness). Cases 2–3
   are exactly that hunt; the audit should also sweep every OTHER
   consumer of `isVariableHeadTypeFamily` for rules that assume
   the current recursor conservatism.

## Ladder after the rule lands

1. `polymorphic_seq_module_rejection` flips from expected-rejection
   to a translation row; emitted `Rev.lean` must elaborate (needs
   `Either#rec` head emission through the existing ctor-order
   assertion machinery — verify `saw_ctor_order` covers Either).
2. `rev.cry` in saw-lean-example: demo step 3 un-`fails`.
3. Stream@core pair (`cryptol_chacha20_{core_iterate,iround_zero}`
   proof-gaps): re-run; the release plan folds them into this
   family, but they may expose the analogous hole at `Stream#rec`
   or a different one (iterate-family fix interplay) — treat as a
   separate verification step, not an assumed win.
4. Full conformance; census delta recorded in STATUS.md.

## Explicitly NOT in scope

- Growing the fix recognizer (FROZEN surface — untouched).
- Direct Nat/Bool/Z/Accessible recursor emission (separate PosRep
  program).
- Any change to `adaptTo` or the emission paths themselves.

## Audit verdict (2026-07-17, two independent Fable auditors)

**Verdict: SAFE-TO-IMPLEMENT WITH CONDITIONS. No silent-wrong-value
path found** — every unsafe instantiation is either
semantics-preserving or LOUD (adaptTo chokepoint or Lean's type
system). The coherence audit (companion doc) additionally found the
bare-vs-applied asymmetry is one cell of a CLASS: ~8 scattered
classifier cascades diverging only on var-headed types.

**Operative design (supersedes candidate A): the KIND-DIRECTED
rule via ONE shared classifier.** A variable-headed type classifies
by the declared result sort of its head's kind (Γ-known):
Type-sort result → value (wrap); Prop/higher → raw. Implemented as
`classifyDomain` + position projections (coherence audit's sketch),
with position-dependence surviving only where principled (Nat
computed-vs-index; recursor elimSort).

**Corrected rationale (design case 3 was WRONG):** SAWCore ADMITS
Prop ≤ sort 0 cumulativity (`Ord Sort`: `PropSort <= _ = True`,
Functor.hs:66; `scmSubtype`/`scmApply`, Certified.hs:1428/498). A
sort-0-kinded head CAN be instantiated at a Prop. Safety rests on
the LEAN BACKSTOP: `Except String P` at `P : Prop` is ill-typed in
Lean 4 (no term cumulativity) → loud. This backstop is part of
`classifyDomain`'s contract and must be documented there so a
future wrapper change cannot silently reopen it.

**Binding conditions for the implementation:**
1. Precise gate — do not reuse `isVariableHeadTypeFamily` for the
   wrap decision; key on the head-kind's RESULT SORT, and the
   recursor arm still consults `elimSort /= propSort` (mirror the
   Nat arm).
2. Document the Lean backstop for Prop (above) in the classifier.
3. Unify with `phaseBetaResultIsValue`'s `isVariableHead ret`
   disjunct — same domain question; if `classifyDomain` doesn't
   subsume it the asymmetry just moves.
4. The Stream@core flip is REAL and intended (`streamGet`'s motive
   `\strm' -> a` is the same shape; the chacha20 rows' immediate
   blocker IS this rule) — but re-classify those rows
   deliberately: they remain gated by the fix
   productivity contract and proof-ergonomics budgets
   (necessary-but-not-sufficient). `stream_fibs`/`stream_step`
   reject at `Prelude.fix` — different hole, untouched.
5. Verify the pre-existing stamp/emission divergence in
   RawValueMode (phase-independent motive classification) is not
   newly reachable for bare-var motives; any divergence is loud.
6. Keep the reject pins green:
   `recursor_wrapped_scrutinee_raw_result_boundary` (Eq-motive)
   routes through the `asEq` arm and must still reject; Either/
   Left/Right + Stream/MkStream head emission verified present
   (SpecialTreatment mappings + ctor-order assertions — the
   scoping claim "only the type maps" was inaccurate but safe).

**Also confirmed:** strict scrutinee semantics match `Bind.bind`
(evalRecursor = vStrictFun); motive wrap placement and case-handler
conventions are consistent; Either#rec head emission completes.

**Doc obligation:** add the var-headed/kind-directed rule to
`2026-07-02_position-callee-calculus.md` as the stated authority —
its silence was the root cause (coherence audit §4).
