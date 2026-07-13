# OP-3: structural lowering for the bounded-vec-fold fix class

**Date**: 2026-07-12. **Status**: **REFUTED BY AUDIT (2026-07-12,
third adversarial Opus audit) — DO NOT IMPLEMENT. Kept as the record
of a rejected candidate so it is not re-proposed.** Verdicts:
Primary REFUTED, A REFUTED, C REFUTED, D REFUTED, B/E
CONDITION-and-defective. Findings:

1. **The recognizer shape does not occur in the corpus.** The real
   normalized bodies of BOTH acceptance targets reference the
   recursive vector as `at n (PairType …) (zip … rec xs) idx` —
   Cryptol compiles parallel comprehensions through `zip`, so `rec`
   flows into `zip` and is never the direct vector argument of `at`
   (running_sum golden lines ~213-238, popcount32 ~287-309). The
   draft's rewrite has no subterm to fire on and is ill-typed at the
   zip element type.
2. **The strict prefix-build is wrong for the accepted class**
   (kernel-checked): the `[seed] # [comprehension]` shape nests
   `at (gen K (\i'' -> … rec …)) (i-1)`; SAW's lazy semantics give
   `at (gen K g) j = g j` (only index j forced), but a strict
   `Vector.ofFnM` build forces ALL K inner elements — including
   later-index references — so every element ≥ 1 of running_sum
   evaluates to the prefix-lookup error instead of SAW's value.
3. **`atWithDefault` default-dropping is unsound** — it is exactly
   the "replace a real default with an error" rewrite OP-2's audited
   binding condition 1 forbids (`j ≥ n` returns `d` in SAW).
4. **Deleting the wrapped contract regresses coverage**: rec_ones and
   stream_fibs (Stream carriers) currently emit via the wrapped
   contract and would fall to hard rejection; ChaCha20-iterate is on
   the RAW path (this draft mis-scoped it as wrapped) and is not
   unblocked by any variant of this design.
5. The novel error string violates OP-2's message-exactness condition
   outside SAW's divergence region (which finding 2 shows it would
   be).

**Minimum conditions for a viable successor** (from the audit): match
the actual `at (zip …) idx` / nested-`gen` shapes; reproduce SAW's
LAZY selection (no strict intermediate gen/zip builds — e.g. a
whole-vector iterate/Kleene construction or the May parametric-bridge
approach `saw_self_ref_comp_iterate`); the recursive handle must be
the full wrapped vector, not a per-index lookup; preserve
`atWithDefault` defaults; reconcile or eliminate any novel error
message; decide the stream rows' fate explicitly before touching the
wrapped contract path.

Original (refuted) draft follows for the record.

---

**Original status**: PRE-AUDIT DRAFT (the audit-first
process applies: adversarial Opus audit before implementation).
Companion to `2026-07-12_obligation-placement-design.md` §Instance 3,
whose post-audit contract analysis this implements via the
STRUCTURAL-FIRST entry decision (TODO.md, 2026-07-12). Reuses the
soundness-chain framing of `2026-05-02_recursion-design.md` (whose
Slice A/B machinery the position-directed rewrite retired) updated to
the Phase-β wrapped value convention.

## Problem

Every wrapped `Prelude.fix` currently lowers to
`saw_fix_choose typeLean body (h_fix_unique_ : saw_fix_unique_exists …)`
(`Term.hs:4417-4434`). That contract is UNSATISFIABLE for every strict
body — errors are always fixed points of eager `Except` bodies
(kernel-checked counterexample in TODO.md) — so the recurrence class
(running_sum, popcount32, rec_ones, stream_fibs, ChaCha20-iterate)
emits obligations that can never be discharged. The obligation-placement
audit additionally refuted the pure-uniqueness replacement with the
divergence witness `fix Bool (\b -> ite Bool b True True)`; its lesson
stands: **no fixed-point predicate over the lifted body can express
productivity**, so the fix must be recognized structurally or rejected.

## Design

### Recognizer (SAWCore side, post-scNormalize)

`classifyWrappedFix tyArg bodyArg` matches exactly one ACCEPT shape:

**BoundedVecFold**:
- `tyArg = Vec n A` with `n` a concrete numeral (SAWCore-side constant
  evaluation; symbolic length REJECTS), `A` a value-domain carrier
  (`shouldWrapBinder tyArg` true — this is the wrapped-fix path).
- `bodyArg = \rec -> gen n' A' (\i -> e)` (or the `genWithProof` form)
  with `n' = n`, `A' = A` up to normalization.
- Every free occurrence of `rec` inside `e` is the VECTOR argument of
  a `Prelude.at n A rec j` (or `atWithDefault n A d rec j`)
  application — never escapes whole, never flows into another
  function. The index expressions `j` are collected but NOT required
  to be statically earlier (see the faithfulness argument for why the
  lowering makes that safe).

Everything else — including `fix` at `Bool` (the audit witness), at
function types, at `Stream` (parked with the Stream@core pair), at
symbolic lengths, and any body whose `rec` escapes an `at`
application — REJECTS with a named diagnostic
(`Prelude.fix: unrecognized recursion shape; the Lean backend lowers
only bounded vector-fold recurrences (recursive references through
Prelude.at on strictly-earlier indices)`). The wrapped-fix CONTRACT
emission is DELETED — it certifies nothing (unsatisfiable) and its
existence invites exactly the unsound "fix the contract" patches the
audit refuted. The raw fix path (`saw_fix_unique_exists_raw`) is
untouched, per the scope table.

### Lowering

The matched body lowers to a call of a new support-library helper
(name chosen to dodge the obsolete-helpers ban list, which pins the
RETIRED May helpers):

```lean
/-- Structural realization of SAWCore `fix (Vec n α)` for the
bounded vector-fold recurrence class. Builds the vector
index-by-index in the Except monad; the body's recursive references
go through `lookup`, which serves only the ALREADY-BUILT prefix —
a reference at `j ≥ i` yields the error below, never a fabricated
value. Productivity of live references is the documented Cryptol
trust link (residual-trust catalog); a non-productive body reaches
the error loudly instead of silently denoting a wrong value. -/
def saw_fixVecFoldM (n : Nat) (α : Type)
    (body : (Nat → Except String α) → (i : Nat) → i < n →
            Except String α) :
    Except String (Vec n α)
```

implemented by structural recursion on the prefix length (the
`Vector.ofFnM`-adjacent pattern already used by `genWithBoundsM`),
where step `i` runs `body (prefixLookup builtPrefix) i h` and
`prefixLookup` returns `pure builtPrefix[j]` for `j < i` and
`Except.error "fix: reference to an index not yet constructed"`
otherwise. Element errors short-circuit the whole build exactly as
`genWithBoundsM` does (monadic bind), preserving SAW's error
propagation.

Emission rewrite: `e' = e` with every `at n A rec j` →
`lookup j`-shaped call (through the position calculus's existing
argument interpretation: `j` translates exactly as an `at` index
would, but the OP-2 at-contract decision DOES NOT APPLY — `lookup`
is total by construction, no bound obligation, no runtime accessor);
every `atWithDefault n A d rec j` likewise (the caller default is
DISCARDED — see audit question D). The binder `i` carries
`h_gen_bounds_ : i < n` exactly as `genWithBoundsM` binders do, and
enters `natBoundsEnv` so interior `at` applications on OTHER vectors
keep their OP-1/OP-2 treatment.

### Faithfulness argument (for the auditor)

SAWCore's only spec for `fix` is `fix_unfold : fix T f = f (fix T f)`
plus the operational lazy-unfolding meaning. For a body in the
recognized class whose live recursive references are productive
(every reference evaluated while computing element `i` lands at
`j < i`):

- By induction on `i`: SAW's `fix` value at index `i` equals
  `e[fix, i]` where every `at fix j` reads a `j < i` element already
  characterized by the induction hypothesis; our build computes
  literally that (`prefixLookup` returns the already-built element).
  Base and step both go through the same `e`, so the vectors agree
  elementwise; both sides propagate element errors through the same
  short-circuit structure.
- If a live reference is NOT earlier (`j ≥ i` reached at runtime):
  SAW's fix diverges (no value); our build yields
  `Except.error "fix: …"`. This divergence-vs-error gap is the
  Cryptol-productivity residual trust (Link 1 of
  `2026-05-02_recursion-design.md`, already in the residual-trust
  catalog) — identical in kind to the May design, but STRICTLY safer
  in degree: the May `genFix` returned the default `d` (a live value
  that could coincidentally prove equalities), whereas an error value
  can never witness agreement with any `pure` result.
- Dead non-earlier references (e.g. the `rec@(i-1)` branch of an
  `ite (equalNat i 0) base step` at `i = 0`) are DISCARDED by the
  strict-but-selecting `iteM` (verified in the OP-2 amendment audit:
  branches are direct arguments; `Bool.rec` selection never forces
  the untaken branch). This is why the recognizer does not need
  guard-aware static earlier-ness: the standard recurrence shapes are
  guard-dead at the boundary, and the lowering is safe either way.

### What this deletes and re-pins

- `lowerWrappedFixProofObligationLean` and the wrapped
  `saw_fix_unique_exists`/`saw_fix_choose` emission path (support-lib
  defs stay for the raw path only if shared; otherwise retire).
- `obligations/fix_wrapped_unique` re-pins to the new lowering or the
  rejection; the Bool witness gets a verbatim litmus row
  (saw-boundary, expect-fail, named diagnostic).
- `proof-gaps/cryptol_running_sum_verify` closes end-to-end
  (ACCEPTANCE): emission through `saw_fixVecFoldM`, discharge proof of
  the recurrence-vs-explicit-sum equivalence, axiom audit clean.
- Support proofs: elementwise characterization lemmas for
  `saw_fixVecFoldM` (`i`-th element equation under in-prefix
  references) as proof support — successors of the retired May
  parametric bridges.

### Audit questions (answer each adversarially)

A. Is the elementwise induction argument sound for ALL bodies the
   recognizer accepts — including bodies where `e` uses `rec` under
   nested binders (inner `gen`, folds) or where the same element is
   referenced twice? Construct a witness if not.
B. Divergence-vs-error: is there a context where the
   `Except.error "fix: …"` value produced for a non-productive live
   reference lets Lean CERTIFY a statement SAW would accept
   differently (not merely fail to evaluate)? (Note the error string
   is NOT a Prelude message — SAW has no corresponding error value;
   is introducing a novel error message itself a faithfulness
   defect? Compare with the audited at-accessor condition.)
C. The recognizer's "rec only under `at`" condition: find an
   accepted body shape where the rewrite `at n A rec j → lookup j`
   changes semantics (e.g. `rec` under `atWithDefault` with a
   MEANINGFUL default that SAW would return for an out-of-range
   index where our lookup errors — SAW's atWithDefault on the FIX
   vector at `j ≥ n` returns `d`, our lookup errors: is that
   reachable in the accepted class, and is dropping `d` sound?).
D. Deleting the wrapped contract path: does any in-scope shape lose
   its only (even if undischargeable) representation, i.e. does
   rejection regress coverage that the contract path nominally
   provided? Enumerate corpus rows currently on the wrapped contract.
E. The Phase-β delta: SAW `fix` at `Vec n A` under the wrapped
   convention receives/produces `Except String (Vec n A)`. Verify the
   recognizer matches the term BEFORE value-domain wrapping (SAWCore
   side), so no wrapped/raw confusion enters the classification; and
   that `saw_fixVecFoldM`'s type sits correctly in the calculus
   (BindingWrapped result, function argument convention for `body`).
