# OP-3 successor design: bounded-iteration lowering for productive fix

**Date**: 2026-07-15. **Status**: PRE-AUDIT DRAFT — the audit-first
process applies: fourth adversarial audit BEFORE any Term.hs change.
Successor to the REFUTED structural draft
(`2026-07-12_op3-structural-fix-design.md`, kept as the
rejected-candidate record); implements
`2026-07-12_obligation-placement-design.md` §Instance 3's two-part
fix under the STRUCTURAL-FIRST entry decision. 0.02 W1 headline
(`2026-07-14_release-plan.md`).

## The six minimum conditions (third audit), restated as obligations

1. Match the ACTUAL normalized shapes: the recursive vector flows
   through `zip` (`at n (PairType …) (zip … rec xs) idx`), and the
   `[seed] # [comprehension]` shape nests
   `at (gen K (\i'' -> … rec …)) (i-1)` — never bare `at rec j`.
2. Reproduce SAW's LAZY selection (`at (gen K g) j = g j`): no
   strict intermediate gen/zip builds — a strict `Vector.ofFnM`
   prefix build forces later-index references and errors on every
   productive element (kernel-checked in the third audit).
3. The recursive handle must be the FULL wrapped vector (the body
   binds it whole: `Bind.bind rec (fun v => … zip … v …)`).
4. Preserve `atWithDefault` defaults (OP-2 binding condition 1).
5. No novel error strings outside SAW's divergence region (OP-2
   binding condition 2).
6. Decide the stream rows' fate BEFORE touching the wrapped
   contract: `rec_ones`/`stream_fibs` are wrapped-contract Stream
   rows; ChaCha20-iterate is on the RAW fix path.

## Design in one paragraph

A conservative, syntactic PRODUCTIVITY RECOGNIZER (gate) classifies
each wrapped `Prelude.fix` body. Recognized FINITE bounded-lookback
bodies lower to a Kleene bounded-iteration construction
`saw_fix_bounded`: iterate the UNTOUCHED translated body n times
from a pure default seed — the body itself is never rebuilt, so
conditions 1-3 hold by construction, and seed-independence of
stabilized prefixes (proved in Lean, once, as library lemmas) gives
the lazy-selection faithfulness that strict prefix-building lacked.
Recognized STREAM corecursion (single-step lookback over `[inf]`)
lowers through the existing MkStream pointwise realization
(`saw_stream_unfold`, the `iterate f x = MkStream (fun n => f^n x)`
family — the retired May parametric-bridge semantics, revived as
checked defs). EVERYTHING ELSE REJECTS with a named diagnostic —
including the audit's Bool divergence witness verbatim. The
`saw_fix_unique_exists` contract is then RETIRED (no emitter), not
revised: no fixed-point predicate can express productivity
(§Instance 3's general lesson), so nothing may emit it.

## Part 1 — the recognizer (gate b, mandatory)

Haskell decides ACCEPT-with-declared-lowering vs REJECT; it never
rewrites the body or proves anything (backend-minimality preserved).
Recognized classes, deliberately narrow:

**Class F (finite bounded-lookback).** The translated body has the
shape the corpus actually produces (condition 1):
`\rec -> <appendShape>` where every occurrence of `rec` in the body
is (i) bound whole (`Bind.bind rec (fun v => …)`, condition 3) and
(ii) consumed only under the append-shifted index family — the
compiled `[c] # [ f | x <- xs | p <- rec ]` pattern where element
`i` of the result reads `rec` only at indices `< i` (in the corpus:
through `at (gen K g) (i-1)` after the append shift, including the
zip-mediated form). The recognizer checks the SOURCE-side fix
argument shape (SAWCore term structure: `append (single c)
(gen n (\i -> body_elt))` with `rec` references inside `body_elt`
occurring only under the shifted projection of the zip/gen family),
NOT the emitted Lean. Anything with a non-shifted index, a computed
index the recognizer cannot bound, multi-step lookback, or `rec`
consumed outside the append arm → REJECT.

**Class S (stream single-step corecursion).** Same append shape at
`Stream` type (`[c] # [ f | p <- rec ]` over `[inf]`), plus the
`iterate`-compiled `fix (\rec -> MkStream-headed …)` family. Lowered
via MkStream index realization (Part 3).

**Reject set.** Everything else, with diagnostic
`unrecognized fix shape: <reason>` naming which condition failed.
Litmus rows: the Bool witness `fix Bool (\b -> ite Bool b True
True)` verbatim; a two-step-lookback comprehension; a fix whose rec
occurs outside the append arm. All expected-rejection rows in
`saw-boundary/`.

## Part 2 — Class F lowering: `saw_fix_bounded`

Support-library definition (names bikesheddable):

```lean
/-- n-fold iteration of the translated fix body from a pure seed. -/
def saw_fix_bounded (n : Nat) (α : Type) [Inhabited-free default d]
    (body : Except String (Vec n α) → Except String (Vec n α))
    : Except String (Vec n α) :=
  Nat.rec (pure (Vector.replicate n d)) (fun _ acc => body acc) n
```

(The default `d` comes from the SAME source the emitted body already
carries — the comprehension's `atWithDefault` defaults, condition 4;
the emitter passes it explicitly, no Inhabited machinery.)

Key properties, proved ONCE in Lean as library lemmas (this is the
faithfulness core — the fourth audit should attack exactly here):

- **L1 (stabilization).** For a body whose element `i` depends only
  on elements `< i` of its argument (stated semantically as a
  hypothesis `H_prod` on the Lean side, discharged per-instance by
  `rfl`-class unfolding of the concrete body):
  `∀ k > i, (saw_fix_bounded-iterates k).get i` is constant in k and
  seed. Formally: `bodyIter (i+1) s₁ =ᵢ bodyIter (i+1) s₂` at all
  indices `≤ i`.
- **L2 (pure survival).** Under `H_prod` with total element
  functions, `saw_fix_bounded n α d body = pure v` for a concrete
  `v` given elementwise success (the analog of
  `vecSequenceM_ok_of_get`) — errors are neither manufactured nor
  dropped: if any element computation errors at its own index, the
  iterate errors exactly there (condition 5: the error strings are
  the body's own).
- **L3 (unfolding agreement / the SAW link).** `body
  (saw_fix_bounded n α d body) = saw_fix_bounded n α d body` under
  `H_prod` — i.e. the construction IS a fixed point of the body.
  This is the statement that ties to SAW's only spec for `fix`
  (`fix_unfold`): SAW's `fix body` and `saw_fix_bounded` are both
  fixed points, SAW's lazy evaluation computes elementwise exactly
  the stabilized values (trust links: Cryptol productivity +
  scNormalize preservation, per the residual-trust catalog — named,
  not manufactured), and L1 pins the elementwise values uniquely
  for bounded-lookback bodies.

Emission: the translator emits `saw_fix_bounded n α d
(translated-body-verbatim)` — the body is the SAME term the current
lowering produces as the contract's body argument (conditions 1-3
free of charge: we never decompose it). NO obligation is emitted.
Discharge of the acceptance goals then proceeds by unfolding
`saw_fix_bounded` (a computable Nat.rec) plus the L-lemmas plus the
existing `foldl_eq_natRec_atWithDefault` bridge (parked May lemma,
revived as the spec-side connector).

**Why this evades the third audit's refutations.** The refuted draft
REBUILT the body as a strict per-element prefix construction —
wrong shapes (condition 1), strict forcing (condition 2), per-index
handle (condition 3), dropped defaults (condition 4), novel error
strings (condition 5). `saw_fix_bounded` rebuilds NOTHING: the body
is applied whole, n times. Laziness objection (condition 2) becomes
L1: strictness of intermediate iterates is harmless because iterate
k+1 only trusts prefix ≤ k of iterate k, which is already
stabilized-pure; the audit's every-element-errors scenario cannot
arise from a PURE seed (that scenario required the error-seeded
prefix build).

## Part 3 — Class S lowering: streams

`rec_ones`/`stream_fibs`/`iterate`: lower to
`MkStream (fun idx => <elementwise closed form via bounded lookback
from index 0>)` — concretely `saw_stream_unfold : (α → α) → α →
Stream α := fun f x => MkStream (fun n => Nat.rec x (fun _ a => f a) n)`
for the iterate family, and the single-step append form as its
special case. This is the pointwise realization the existing
`saw_mkStream_total_exists` machinery already contracts for; no new
trust class. The Stream@core boundary rejections (the ChaCha20 pair,
`polymorphic_seq_module_rejection`'s stream half) re-open AFTER
Class S lands: their recursor-convention hole (raw result demanded
from Except-wrapped scrutinee) is a separate item this design only
UNBLOCKS, tracked as the ladder's step 5 — this doc does not claim
it.

## Part 4 — retirement and migration

- `saw_fix_unique_exists` loses its last emitter → deleted with its
  choose lemmas (`saw_fix_choose`); `obligations/fix_wrapped_unique`
  re-pins as a Class-F structural emission row;
  `saw-boundary/fix_obligation` family re-pins on the new
  diagnostics. The raw fix contract (`saw_fix_unique_exists_raw`)
  is explicitly untouched (per Instance 3) and ChaCha20-iterate's
  raw-path fate rides Class S + the recursor-convention follow-up.
- Acceptance ladder (in order, each a commit-gated slice):
  `cryptol_running_sum_verify` discharges end-to-end →
  `offline_lean_popcount32` + E6 → `llvm_popcount_eq` →
  `rec_ones`/`stream_fibs` module rows → Stream@core/Either@core
  path re-opened → `rev.cry` module translation (demo step 3).
- Litmus/negative rows land in the SAME slice as the recognizer
  (gate before lowering).

## Questions the fourth audit should attack

1. Is L1's per-instance `H_prod` discharge (`rfl`-class unfolding of
   the concrete body at each index) actually closable for the
   running-sum body without heartbeat inflation, or does it need
   per-shape lemmas the library lacks?
2. Does the pure-seed iterate REALLY avoid the strict-forcing trap
   for the zip-mediated shape — i.e., is `bodyIter 1 (pure default)`
   elementwise-pure for the REAL running_sum body (whose element
   binds go through `Bind.bind rec`), or does some element of
   iterate 1 error on the default prefix in a way L2's hypothesis
   cannot exclude?
3. Is the recognizer's source-side shape check implementable without
   emitted-Lean inspection and without false ACCEPTs on computed
   indices (the calculus's never-classify-by-emitted-AST rule)?
4. Does the default `d` threading violate condition 4 in bodies
   whose own `atWithDefault` default differs from the
   comprehension's seed element?
5. Is condition 6 fully satisfied — do `rec_ones`/`stream_fibs`
   actually fit Class S's single-step form, or do they need the
   append-at-Stream shape the recognizer must treat separately?
6. Trust-link honesty: does L3's argument add any trust NOT already
   in the residual catalog?
