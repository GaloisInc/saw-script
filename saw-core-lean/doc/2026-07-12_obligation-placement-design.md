# Obligation Placement & Satisfiability

**Date**: 2026-07-12. **Status**: design for the current operative
priority (TODO.md). Successor program to the position-directed
translation plan (`2026-07-08_position-directed-translation-plan.md`,
complete).

**Audit record (2026-07-12, adversarial Opus audit before any
implementation):** OP-1 SOUND as written; OP-2 SOUND subject to two
conditions now stated inline (runtime lowering restricted to `at`;
Prelude-exact error string); the ORIGINAL OP-3 (uniqueness among pure
fixed points, unconditionally emitted) had a real soundness hole —
witness `fix Bool (\b -> ite b True True)`: unique pure fixed point
`true`, but SAWCore's lazy `fix` diverges on it, so the contract would
have been dischargeable for a term whose SAW meaning is undefined. The
OP-3 section below is the post-audit revision; the pre-audit text
(including the false claim "excluding error fixed points from the
uniqueness quantifier removes no safety") is superseded. The audit also
added the obligation-site scope table at the end.

## Principle

Every obligation the backend embeds inside an emitted term must be
**provable at its emission position** — either discharged there by a
checked tactic over facts in scope, or received as evidence from a
caller that has those facts. `sorry` is acceptable only in the
`theorem goal_holds : goal := by sorry` stub, which is the one
obligation deliberately handed to the user.

Why this is the release bar: the backend's only purpose is discharging
SAW proof obligations in Lean's kernel. An emission that elaborates but
contains an unprovable embedded obligation is *sound but
undischargeable* — no theorem can ever be checked against it sorry-free,
so the backend silently fails at its purpose while every fence stays
green. The 2026-07-12 assessment found three such surfaces; all are
instances of misplaced obligations, none are translator-representation
bugs.

The dual rule already holds and must keep holding: the check stage
(proof harness, differential harness) rejects artifacts whose
obligations remain `sorry`. This design makes emission meet the bar the
check stage already enforces.

## Instance 1: derivable side conditions get a checked tactic (OP-1)

**Defect.** `boundsProofScript` and `partialOpProofScript`
(`src/SAWCoreLean/Term.hs:2626-2640`) emit

```
(try unfold h_..._obligation_); (first | assumption | skip); all_goals sorry
```

`assumption` closes only bounds that appear verbatim as a
`genWithBoundsM` binder hypothesis. Derived indices (`subNat 3 i < 4`
under `i < 4`), constant bounds (`0 < 8` with nothing in scope), and
macro-obscured numerals all fall to the `sorry`. Consequences measured
on 2026-07-12: 19 of the 39 differential known-gap rows pin on
`declaration uses 'sorry'`; every raw artifact with a derived index
carries `sorryAx` inside its goal statement until a user hand-completes
the outline (`proofs/E5_littleendian/completed.lean` is the worked
example of what the emitter should have done itself).

**Fix.** The evidence chain gains a checked arithmetic step, validated
by the completed-outline work that closed E4/E5/offline_t6:

```
(try unfold h_..._obligation_);
first
  | assumption
  | omega
  | (simp only [natPos_macro, bit0_macro, bit1_macro, one_macro,
                zero_macro, succ_macro, subNat, addNat, mulNat,
                Nat.sub_eq] at *; omega)
  | skip
all_goals sorry
```

Notes fixed by experiment during E5 and validated against all six
obligation shapes on 2026-07-12: `omega` does not recognize bare
`Nat.sub`/`Nat.add`/`Nat.mul` applications produced by unfolding the
reducible `subNat`/`addNat`/`mulNat`, so `Nat.sub_eq`/`Nat.add_eq`/
`Nat.mul_eq` are mandatory in the normalization set (full set:
`natPos_macro, bit0_macro, bit1_macro, one_macro, zero_macro,
succ_macro, subNat, addNat, mulNat, minNat, maxNat, Nat.sub_eq,
Nat.add_eq, Nat.mul_eq`); the numeral macros are `@[simp, reducible]`
but `omega` atomizes them unless simp runs first; `simp only … at *`
errors when it makes no progress, hence the bare `omega` alternative
before it. The trailing `sorry` remains as the loud last resort for
obligations that are genuinely not arithmetic. Post-audit caveat: OP-1
does NOT clear every chain it touches — a genuine runtime bitvector
divisor's nonzero obligation (`partialOpProofScript` consumers) is not
omega-closable and correctly stays a loud `sorry`, as do the Instance-2
eta positions until OP-2 lands and the Instance-3 fix contracts until
OP-3 lands; see the scope table. The check stage's rejection of
residual `sorry` is unchanged.

Audit findings incorporated (both SOUND): the emitted obligation Props
are constructed from the checked helpers' own preconditions
(`i < n` for `at`, `off+len ≤ n` for slice — identical to the latent
SAWCore obligation per `Prelude.sawcore`'s `at`/`atWithDefault`
definitions), so the chain cannot mask a semantic obligation behind an
arithmetically-true-but-semantically-false Prop — Prop = helper
requirement = source obligation. And the tactic block cannot alter the
theorem being proven: it only inhabits a `let`-bound Prop fixed before
the tactic runs, and proof irrelevance blocks evidence-term leakage
into the goal's definitional unfolding (the `h : i < n` flows only into
`getElem` bounds witnesses, which are propositional).

The unsafeAssert evidence script (`proofObligationPlaceholder` used at
`h_unsafeAssert_`) gains a `rfl` step for the reflexive `Eq Num x x`
shapes it actually emits:

```
(first | rfl | skip); all_goals sorry
```

**Trusted base**: unchanged. `omega`/`simp only`/`rfl` produce kernel
proof terms at elaboration time. This is not "Lean automation to make
examples pass" in the sense banned by the example-refresh goal — that
ban governs discharging `goal_holds`; this is the emitter supplying its
*own* side-condition evidence, which was always the intent of the
`(first | assumption | …)` chain.

**Migration.** Emission-changing everywhere obligations are emitted:
expect a large reviewed golden refresh. Per-row work: for each of the 19
`sorry`-pinned differential rows, re-run; rows whose artifacts become
sorry-free must have `.known-gap` removed and pass as true differential
coverage; rows still blocked (fix contracts, eta positions, other
causes) keep their pin with an updated diagnostic. Proof rows: the
completed outlines in `proofs/{E4_map_id,E5_littleendian,offline_t6}`
become redundant where the raw artifact is sorry-free — keep
`completed.lean` files that still teach the workflow, delete those that
merely duplicate the emitted chain, and record the decision per row.

**Acceptance.** Conformance green; the un-gapped rows run as true
differential rows; no artifact in the corpus contains an evidence
`sorry` whose obligation is closed by the new chain's tactics when run
manually.

**Implementation record (2026-07-12, OP-1 SHIPPED).**

- The chain landed as specified plus one validated extension: `omega`
  atomizes bare `Nat.div`/`Nat.mod` exactly as it atomizes `Nat.sub`
  (it recognizes division/modulus by a constant only through the
  `HDiv.hDiv`/`HMod.hMod` spelling), and core Lean has no
  `Nat.sub_eq`-style bridge for them. Four `rfl` bridging lemmas were
  added to `SAWCorePrimitives.lean` (`divNat_eq_div`, `modNat_eq_mod`,
  `divNat_checked_eq_div`, `modNat_checked_eq_mod`) and joined the simp
  set. Kernel-validated on the emitted term-level `let` structure
  (`#print axioms` = propext, Quot.sound only). This closes
  checked-division index shapes (`divNat_checked i 2 h < 4` under
  `i < 8`), which un-gapped `differential/cryptol_ec_transpose`.
- Nine differential rows un-gapped into true coverage (census 77→68):
  cryptol_ec_at_literal_branches, cryptol_ec_reverse,
  cryptol_ec_sequence_update, cryptol_ec_transpose, cryptol_indexing,
  sequence_map_zip, sequence_take_drop_update, vector_literal,
  vector_literal_edges.
- **New named surface for OP-2 — guard-dependent branch obligations.**
  Three surviving rows (cryptol_bv_entrypoints, cryptol_ec_sequence_split,
  sequence_append_reverse) pin on bounds of the shape `i < k` emitted
  inside the true branch of `iteM (ltNat i k …)` under only a weaker
  binder hypothesis (`i < n`, `k < n`). The guard semantically
  justifies the bound, but the branch emission does not receive it as
  evidence, so the obligation is unprovable in place — exactly the
  Instance-2 defect in a second costume. OP-2's runtime-checked
  accessor resolves it (guard true ⇒ index in range ⇒ no error; the
  strict `iteM` discards the untaken branch's value, so error-faithful
  lowering preserves SAW's value-or-error meaning). Any OP-2
  alternative that keeps proof-carrying access here must instead
  thread the guard into the branch as a hypothesis.
  `differential/bitvector_order_width` is the value-dependent cousin
  (`0 < x__…` over a runtime bvToNat-derived Nat) — same remit.
  `differential/bitvector_division` stays pinned on concrete-vector
  nonzero facts (`bvNonzeroM` on literal vectors behind shared lets),
  which is the parked crypto-BV automation policy, not an OP-1/OP-2
  matter.
- **Completed-outline redundancy decision: keep them.** The proof
  harness's staging scan is textual, and the OP-1 chain deliberately
  embeds `all_goals sorry` as its loud last resort even when the chain
  closes — so every obligation-bearing artifact still routes through
  `completed.lean`. Making raw artifacts eligible would need a
  `sorryAx`-based scan (elaborate and inspect, as the differential
  harness already does); noted as optional follow-up, not blocking.
- Golden refresh note: the sweep also caught up ~40 rows of latent
  drift from the Slice-7 value-domain rule (pure unit/pair values no
  longer sequenced through `Bind.bind`). The previous conformance fence
  had been run against a stale binary that predated Slice 7's final
  committed state, so the goldens matched the binary but not HEAD;
  verified by rebuilding clean HEAD without the OP-1 edit and
  reproducing the same structural diff. All catch-up hunks correspond
  to committed, reviewed translator changes and re-elaborated green.

## Instance 2: evidence-less checked access must not fabricate (OP-2)

**Defect.** The prefix-partial checked-access convention eta-expands a
partially-applied `at` into

```
fun (η_checked_arg_0 : Nat) =>
  let h_bounds_obligation_ : Prop := η_checked_arg_0 < n;
  let h_bounds_ : h_bounds_obligation_ := (by … sorry);
  atWithProof_checkedM n α xs η_checked_arg_0 h_bounds_
```

The lambda claims `∀ η, η < n` — false for general `Nat`, so *no*
tactic can close it; only `sorry` inhabits the position. In the
saw-lean-example `implRev` goals the wrapper is consumed by an
`Either.rec` over an Int sign-split (`xs @` computes its index through
`natToInt`/`intSub`/`intToNat`), so the true bound is a non-local
arithmetic fact about the sign-split scrutinee. OP-1's local tactic
cannot and should not try to prove it.

**Fix.** Positions that HAVE evidence keep the proof-carrying form —
`genWithBoundsM` binders and concrete indices flow their proofs to
`atWithProof_checkedM` exactly as today. Positions that DON'T have
evidence at emission stop pretending: they route through a
runtime-checked accessor

```
atRuntimeCheckedM (n : Nat) (α : Type)
    (xs : Except String (Vec n α)) (i : Nat) : Except String α :=
  do let vec ← xs
     if h : i < n then pure vec[i]
     else throw ("at: index " ++ … ++ " out of bounds")
```

This is not the banned defaulting fallback: SAWCore's `at` is partial
and its out-of-range meaning IS an error — audit-verified against the
Prelude: `at n a v i = atWithDefault n a (error a "at: index out of
bounds") v i` (`Prelude.sawcore:1563-1564`) — so an `Except.error`
out-of-bounds result is the *faithful* translation of the source
semantics, in the same way the 4a `IndexArg` convention binds wrapped
indices error-preservingly. The proof-carrying form remains the
preferred refinement wherever evidence exists; the runtime check is the
honest form where it does not. Emitted artifacts become sorry-free and
executable, which also lets differential rows evaluate these shapes.
The obligation resurfaces at the correct place: the runtime-value
equality carrier is `Except String T`, so the user's goal proof must
show live error branches dead — the same placement division-by-zero
already commits to.

**Audit conditions (binding):**

1. **The runtime-checked lowering fires for the `at` contract ONLY.**
   The checked table also routes `atWithProof`, `updWithProof`,
   `sliceWithProof`, `updSliceWithProof`, `genWithProof`; of these only
   `at` has error-default Prelude semantics. `atWithProof` is a
   proof-carrying primitive that is total *given its supplied proof* —
   its index slot is never evidence-less (the proof is an argument).
   `atWithDefault` with a genuine caller default keeps that default
   (`atWithDefaultM`); replacing a real default with an error would be
   an unsound rewrite, exactly the class this design exists to prevent.
2. **The runtime accessor's error string is Prelude-exact:**
   `"at: index out of bounds"`, byte-for-byte. The Except-String
   carrier compares error *messages*; a divergent message would make
   Lean distinguish computations SAW deems equal.

**Convention change** (position-calculus terms): the checked-access
`ArgMode` table gets two lowerings for the index slot — `IndexArg` with
evidence (present convention) and `IndexArg` without evidence (runtime
check). Which one fires is decided by the position: an index slot
filled under a binder that carries `h_gen_bounds_`-style evidence, or by
a literal with a decidable bound, lowers checked-with-proof; an
eta-expanded formal or any other evidence-less position lowers
runtime-checked. No emitted-term inspection: the decision reads the
production record / binder environment, per the calculus.

**Acceptance.** saw-lean-example invol/eq_spec goals emit sorry-free,
and their proofs (the reduction recipe already written in
`saw-lean-example/proof/*/proof.lean`) discharge; the
`obligations/vector_at_partial_function` pin updates to the new shape;
no `η_checked` lambda in the corpus contains an evidence `sorry`.

## Instance 3: the wrapped-fix contract must be satisfiable (OP-3)

**Defect.** `saw_fix_unique_exists`
(`lean/CryptolToLean/SAWCorePrimitives.lean:857`):

```
∃ x : α, body (pure x) = pure x ∧ ∀ z : Except String α, body z = z → z = pure x
```

The uniqueness clause quantifies over all `Except` values. Any emitted
body that strictly consumes its recursive argument — every real
self-referential comprehension — propagates `Except.error` through its
element binds, so `body (error e) = error e` for every `e`: errors are
always fixed points, and the obligation is refutable. Kernel-checked
counterexample (2-element running-sum analogue) recorded in the
2026-07-12 TODO entry. Consequence: the recurrence class
(`cryptol_running_sum_verify`, `offline_lean_popcount32`,
`cryptol_module_rec_ones`, `cryptol_module_stream_fibs`, the ChaCha20
iterate pair) emits obligations that can never be discharged. The
primitive's doc comment treated error fixed points as a safety feature
without noticing they always exist for strict bodies.
`saw_mkStream_total_exists` (pointwise totality) and the raw fix
contract are not affected.

**Rejected candidate (audit hole — recorded so it is not re-proposed).**
The first draft proposed uniqueness among pure fixed points,
unconditionally emitted:

```
∃ x : α, body (pure x) = pure x ∧ ∀ y : α, body (pure y) = pure y → y = x
```

The audit refuted its soundness with a concrete witness:
`fix Bool (\b -> ite Bool b True True)`. Well-typed, passes the
polymorphism gate, reaches the wrapped-fix lowering. Its lifted body is
`body z = z >>= fun _ => pure true`, whose unique PURE fixed point is
`true` — the contract is provable and `saw_fix_choose` would denote
`pure true`. But SAWCore's `fix` is a primitive whose only spec is the
unfolding axiom (`fix_unfold`, `Prelude.sawcore:190`) and whose
operational meaning is lazy unfolding: `ite` forces its scrutinee, so
this term DIVERGES — SAW assigns it no value. The contract would let
Lean certify statements about `pure true` for a term whose SAW meaning
is undefined: a silent-unsoundness surface. The general lesson: no
fixed-point predicate over the whole lifted body can distinguish "SAW's
lazy fix computes this value" from "SAW's lazy fix diverges but this is
the only pure fixed point" — that distinction is *productivity*, which
is a property of how the body consumes its recursive argument, not of
its fixed-point set. (A finite-unfolding contract fails differently:
the real workload's bodies are strict — `Vector.ofFnM` short-circuits —
so iteration from an error seed never reaches a pure value.)

**Fix (post-audit).** Two-part design; part (a) is the contract change,
part (b) is the sound gate that makes (a) emittable at all:

(a) For fix shapes the backend RECOGNIZES as productive — the bounded
vector-fold recurrence (a `gen`/`genWithBoundsM` body whose recursive
references go through strictly-earlier indices; the popcount /
running-sum / ChaCha20-iterate class) and the stream-corecursion shape
already covered by `saw_mkStream_total_exists` — lower structurally
where practical (the `genFix`-style construction: productive by
construction, definitionally reducing, no fixed-point obligation, no
`Classical.choose`), and where the structural lowering is not yet
practical, emit the pure-uniqueness contract above. Under the
productivity gate the contract IS sound: for a productive body, SAW's
lazy fix terminates on each element and its value is a pure fixed
point, so uniqueness pins x to SAW's own value. This soundness rests
explicitly on the Cryptol-productivity and `scNormalize`-preservation
trust links already in the residual-trust catalog
(`2026-05-02_residual-trust.md`); the design does not manufacture new
trust, it names where the existing trust is load-bearing.

(b) Every fix shape the recognizer does NOT classify as productive is
REJECTED with a named diagnostic — never given a dischargeable
contract. This keeps the Bool witness (and every future
non-productive shape) on the loud-failure side of the line. The
recognizer is a rejection gate in the established sense (like the
recursor gates), not a semantic rewriter: "Haskell stays dumb" is
preserved because Haskell only decides ACCEPT-with-declared-lowering
vs REJECT, and everything accepted is still checked by Lean.

The structural lowering (a) is the preferred endpoint — it was the
blessed design in `2026-05-02_recursion-design.md` and was shelved for
implementation fragility, not soundness; the position calculus that
now exists removes most of that fragility. Whether OP-3 lands as
structural-first or contract-first-then-structural is an
implementation-order decision to make at OP-3 entry, with the gate (b)
mandatory in either variant.

**Migration.** Productivity recognizer + rejection diagnostic + litmus
rows for rejected shapes (including the Bool witness verbatim);
structural lowering or gated contract + choose/iota lemmas;
`obligations/fix_wrapped_unique` and the stream/fix rows re-pin;
discharge lemmas (`genWithBoundsM` of pure elements = `pure ∘
Vector.ofFn`, elementwise characterizations) added as proof support —
the modern successors of the retired May-era `genFix` parametric
bridges. The raw fix contract (`saw_fix_unique_exists_raw`) is NOT
revised here; it has no error-fixed-point defect but shares the
divergence-vs-uniqueness caveat and stays behind its existing
rejections until it gets the same treatment.

**Acceptance.** `proof-gaps/cryptol_running_sum_verify` closes
end-to-end: SAW emits, the outline completes with checked tactics, a
proof discharges the recurrence-vs-explicit-sum equivalence, the axiom
audit passes. That example was chosen in its GAP note as "the small
version of the popcount-style recurrence shape"; closing it is the
evidence the recurrence class is unblocked.

## Obligation-site scope table (audit-complete inventory)

Every embedded-obligation emission site in `Term.hs`, and what this
program does with it:

| Site | Obligation | Provable at position today? | Disposition |
| --- | --- | --- | --- |
| `boundsProofScript` (`h_bounds_`) | `i < n`, `off+len ≤ n` from checked-helper contracts | Derivable ones no (chain too weak) | OP-1 closes derivable; OP-2 removes the evidence-less eta family |
| `partialOpProofScript` (`h_nonzero_` etc.) | divisor nonzero | Concrete yes, runtime-symbolic no | OP-1 closes concrete; symbolic stays a LOUD `sorry` — correct: it is a real goal-level obligation |
| `h_unsafeAssert_` | `Eq Num x x` shapes | Reducible-reflexive yes | OP-1 adds `rfl`; symbolic non-reflexive stays loud `sorry` |
| `h_fix_unique_` (wrapped) | `saw_fix_unique_exists` | NO — refutable for strict bodies | OP-3: productivity-gated structural lowering / gated contract + rejection |
| `h_fix_unique_` (raw, `saw_fix_unique_exists_raw`) | raw unique fixed point | shares divergence caveat | untouched; stays behind existing rejections; future OP-3 treatment |
| `h_mkStream_total_` | `saw_mkStream_total_exists` (pointwise totality) | yes for productive streams | sound as-is (no fixed-point choice); dischargeability rests on the same productivity trust as OP-3(a) — proof-support work, not a contract defect |
| `h_raw_error_` | `False` (unreachable-branch contract) | only when genuinely unreachable | AUDIT ACTION: verify every in-corpus raw-error position is unreachable-with-context; a REACHABLE raw `error` must reject per the calculus, not emit an undischargeable `False` |
| `h_proof_` (`lowerProofPrimitiveContract`, 14 rows) | proof-primitive props | no (unrealized) | out of scope; loud `sorry` is the honest state until the proof-primitive realizations land |

## Sequencing

OP-1 → OP-2 → OP-3, strictly. OP-1 is mechanical, audited SOUND, and
shrinks the `sorry` surface so OP-2's and OP-3's diffs are reviewable;
OP-2 is a convention change inside the existing calculus machinery
(audited consistent: the evidence/no-evidence split reads the `ArgMode`
table, arity, and binder environment — the eta case is exactly
`bindMissing` on an `IndexArg` — with no emitted-term inspection);
OP-3's contract question is settled above but its implementation-order
variant (structural-first vs gated-contract-first) is decided at OP-3
entry. The `h_raw_error_` audit action rides with OP-2 (same
reachability analysis). Each slice: emitted-corpus diff reviewed
hunk-by-hunk, conformance green with known gaps re-pinned honestly,
smoketest green, drivers refreshed only after per-file review.

## Explicitly out of scope

- Direct-recursor / PosRep program (design exists, no organic workload).
- `proof_*` proof-primitive realizations (14 obligation rows).
- Crypto-grade BV automation (the strict trusted-base policy stands).
- `offline_lean` replay UX (P4 in the assessment; after this program).
- The Either@core / Stream@core recursor-convention decision — related
  (it blocks whole-module translation of polymorphic comprehensions,
  pinned by `saw-boundary/polymorphic_seq_module_rejection`) but a
  separate recursor-convention design, queued behind this program.
