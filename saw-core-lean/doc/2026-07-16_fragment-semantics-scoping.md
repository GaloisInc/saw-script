# Scoping: a provable core for the OP-3 successor (fragment reference semantics)

**Date**: 2026-07-16. **Status**: SCOPED, not scheduled. Sequencing
recommendation: after R4 closes the W1 program; pull forward only if
further audits find recognizer/lowering seam flaws.

## Why this exists

Every adversarial audit of the fix program (third, fourth, fifth) has
attacked the same seam: the EAGER translated body vs SAW's LAZY
elementwise evaluation of a fix. The design's answer so far is
audit-hardened argument plus per-instance proven obligations (loud
failure on wrong verdicts). This document scopes the upgrade from
audited argument to THEOREM for the part that is provable without a
semantic model of SAWCore — which does not exist and is out of scope
(the Rocq backend carries the identical residual trust).

## The crux, stated precisely

SAW's fix at `Vec n α` does not live in the flat domain of whole
wrapped vectors: the least fixed point of the eager translated body
there is ⊥ (the body forces its whole argument — third audit). SAW's
meaning lives in the POINTWISE domain — the n-fold product of flat
element domains, where element i can be defined while element j is
⊥. The load-bearing claim of the whole emission strategy is:

> For bodies with (semantic) bounded lookback, the pointwise-lazy
> least fixed point is TOTAL and equals the n-fold eager iterate
> from any pure seed.

This is a statement about a small closed combinator fragment
(`gen/at/zip/ite/fix/MkStream` + bv ops as opaque element functions),
not about SAWCore at large. It is statable and provable entirely in
Lean. Elements are flat domains, so Kleene chains stabilize in ≤ n
steps: no domain-theory library is needed; the construction is
finitary/constructive.

## Phase A — fragment semantics + adequacy theorems (SMALL; the prize)

Define in Lean (new file, e.g. `SAWCoreFixSemantics.lean`, proofs-only
— no emitter dependency):

* the pointwise element domain `Option α` (⊥ = undefined) and the
  approximation order on `Vec n (Option α)` / `Nat → Option α`;
* the lazy elementwise interpretation of a fix body given as an
  element function `E : (index) → (prefix reads) → α` with lookback;
* `lfp` as the n-th Kleene iterate (stabilization is finitary).

Theorems:
* **A1 (Vec adequacy)**: semantic bounded lookback → lfp is total
  and its totalization equals `saw_fix_bounded_iter_from n α s body n`
  for every seed `s` — tying the EXISTING library realization to a
  least-fixed-point characterization, not just to fixed-point-ness
  plus uniqueness.
* **A2 (Stream adequacy)**: the analog for `saw_stream_unfold`
  (index induction; lfp of the single-step lazy body is total and
  pointwise-equals the realization).
* **A3 (negative sanity)**: the audits' Bool divergence witness has
  lfp ⊥ — the model itself rejects it, independent of H_prod being
  unprovable.

Estimated size: a few hundred lines of manual Lean; re-derives the
R1 stabilization lemmas FROM an lfp definition, which is what makes
it adequacy rather than consistency. Axiom budget: standard trio at
most.

## Phase B — shape-witness reification (MEDIUM)

A Lean inductive mirroring the recognizer's accepted grammar
(Class F fused gen/ite with -1 shift; Class S-single identity read),
plus one theorem per class: every witnessed shape's translated body
satisfies the per-instance obligation (H_prod /
`saw_stream_single_productive`). Consequences:

* per-instance discharges become instantiation, not hand-proof;
* the Haskell gate and the Lean-validated grammar become
  DIFF-TESTABLE (emit the witness alongside the realization) —
  closing the exact seam where the fourth and fifth audits found
  gate-broader-than-lowering flaws, by construction.

## Phase C — differential validation of the residue (CHEAP, incremental)

What remains unprovable in principle without formalizing SAWCore:
(i) SAW's evaluator implements the pointwise-lazy fragment semantics;
(ii) `scNormalizeForLean` preservation (§3.3). Both are
differentially testable: add fix-specific `differential/` rows that
evaluate recognized shapes CONCRETELY on both sides (saw eval vs
Lean `#eval` of the realization) across the recognized-grammar
corners (seed boundary, lookback boundary, error-in-element).

## Honest limits (named, per catalog discipline)

* The SAWCore/Cryptol elaboration link stays TRUST, not theorem —
  no formal SAWCore semantics exists anywhere; building one is a
  separate research-scale project.
* The Cryptol-semantics-in-Coq line of work is a conceivable future
  anchor for the Cryptol-productivity link (residual-trust Link 1),
  but connecting it formally is out of scope here.
* Phase A does NOT discharge residual-trust §3.2/§3.3; it shrinks
  §3.2's argument surface: "realization = lazy lfp of the fragment
  body" becomes a theorem, leaving "SAW evaluates the fragment
  lazily as modeled" as the named trust, which Phase C then tests.

## Sequencing

R3b flip → R4 retirement first (the current discipline is
sound-by-loudness; nothing here blocks it). Phase A is the first
0.03-class candidate; Phases B/C ride behind it. Pull Phase A
forward if any further audit finds a seam flaw — at that point
proof replaces adversary on the semantic side.

## The "lux" endpoint (thought experiment, recorded 2026-07-16 — NOT scheduled)

The maximal version of this program: (1) deep-embed the SAWCore AST
in Lean with an interpreter; (2) differentially test that interpreter
against the real SAW implementation; (3) prove the emission strategy
correct against the deep embedding (the translator gains a SPEC —
or, cheaper, per-emission translation validation). Assessment:

* Coherent and precedented (verified-translator architecture;
  Galois's cryptol-semantics Coq project did the methodology for
  Cryptol — subset coverage, person-years, eventual bit-rot).
* The interpreter cannot cover SAWCore-as-type-theory (general
  recursion forces fuel semantics; the dependent layer needs
  induction-recursion Lean lacks). Every realistic version retreats
  to the evaluator's VALUE fragment — i.e. the fragment this doc
  already scopes, deep instead of shallow.
* Step 2 remains empirical even in lux: "interpreter ≡ SAW" never
  becomes a theorem. Lux narrows the trust to one artifact; it does
  not eliminate the class.
* Deep-embedding obligations are unusable raw; the standard adequacy
  layer ("deep ⟦t⟧ = shallow(t)" on a fragment) RECONSTRUCTS the
  current emission strategy as lux's usability layer.

DESIGN CRITERION (binding on any phase that builds reference
semantics, incl. Phase A): the deep/reference side must be optimized
for EVIDENT correctness — transcription-closeness to the SAWCore AST
and the evaluator's actual rules (mfix-over-thunks, elementwise
Thunk vectors, escaping errors) — NEVER for provability. The
reference is the "obvious but awkward" semantics; the emission is
the "nice but not-obvious" one; the adequacy theorems are the bridge
that purchases the nice from the obvious, and ALL proof burden
belongs on the bridge. Making the reference nicer to prove against
moves correctness-burden back into the spec and defeats the program.

Consequence adopted: Phases A/B/C are lux restricted to where it
pays — A = the deep semantics on recognized shapes, B's witness
inductive = a deep embedding of the recognizer grammar with step 3
restricted to it, C = step 2. The growth path is monotone (widen
witness grammar and fragment semantics together); design Phase B's
witness datatype so it can serve as the deep-embedding seed if the
program ever escalates.

## Zone anatomy (2026-07-16): where bugs CAN live, by construction

The soundness story is not one mechanism but three, on three regions.
This is the canonical statement of "if there are bugs, they are
outside a well-behaved fragment we can characterize."

**Zone 1 — the total fragment.** Total combinators over total
element operations; no fix, no reachable runtime check, no error.
Emission is HOMOMORPHIC here: the Except layer is inert, eager and
lazy coincide, the error-refinement direction is never exercised.
Structural consequence: no emergent interactions — a bug can only be
a per-combinator mistranslation, which is exactly the class the
definition audits (realization vs Prelude.sawcore definition) and
the differential rows (observational agreement with SAW's evaluator)
cover. Residual risk: a consistent-since-day-one mistranslation in a
combinator corner no differential row exercises — internally
uncatchable in principle, so Zone-1 confidence IS the differential
coverage census (kept as a live artifact next to this doc; the
release audit already named 11 zero-coverage helpers).
Self-certification note: every green proof row proves both goal
sides reduce to pure values — each discharge certifies its own
instance's Zone-1/gated-Zone-2 membership.

**Zone 2 — the partiality frontier.** fix, error routes,
runtime-checked access, computed conditions. Domains genuinely
diverge (eager Except vs thunks + escaping exceptions); interactions
are emergent. EVERY theory bug found to date (pure-uniqueness hole,
strict-prefix refutation, fourth-audit seed/totality amendments, R0
reverse-spine laxity, fifth-audit step-extraction gap) is a Zone-2
fix-seam bug; zero were Zone-1 semantic bugs. The design's response
is containment, not correctness-by-fiat: recognizer gates +
per-instance PROVEN obligations + uniqueness theorems convert
soundness bugs into COMPLETENESS bugs. The loud-failure invariant
holds under three named conditions — a silent Zone-2 bug requires
one of them to fail:
  1. verbatim-body discipline (obligations against the untouched
     translated body — fifth audit);
  2. model grounding (lazy-lfp / pointwise / error-refinement
     reading of SAW — evaluator grounding record §3.2a, pinned
     continuously by Phase-C fix/error differential rows);
  3. uniqueness coverage (the per-class theorems pinning the
     realization as THE value).
All five historical bugs were caught before any emission depended on
them — the audit-first and recognizers-land-inert-first patterns
create the window where classification can be wrong while emission
cannot. Keep both patterns mandatory.

**Zone 3 — the reject set.** Loud by construction; bugs are
availability bugs only.

The zone BOUNDARY is the recognizers — which is why Phase B (witness
reification: gate mechanically coincides with the validated grammar)
is the highest-leverage item in this program.

## Certificate-tier architecture (2026-07-16): evidence-conditioned well-behavedness

Decision-candidate recorded from design discussion: condition the
backend's guarantee on TERMINATION/DEFINEDNESS EVIDENCE, supplied as
kernel-checked proof — never as assertion, hypothesis, or axiom.

Precisions:
* The unified condition is DEFINEDNESS OF THE LAZY LEAST FIXED POINT
  (totality of the limit in the pointwise semantics) — subsuming
  termination (Vec: stabilization ≤ n), productivity (Stream: every
  element defined), and error-freedom in forced positions. "The user
  supplies evidence" is already the design's shape: per-instance
  H_prod obligations ARE local, kernel-checked definedness evidence;
  there is deliberately no global "input terminates" precondition —
  a global assumption is a silent-failure surface, locality + proof
  is not.
* TWO-TIER GATE (the architectural upgrade this implies, gated on
  Phase A existing):
  - General tier (semantic): for ANY wrapped fix, the user may
    supply a proof in the fragment reference semantics that the
    pointwise-lazy Kleene chain of the fix's EMITTED WITNESS (a deep
    embedding of its SOURCE shape) stabilizes at a total value; the
    realization is that value. Same residual trust as the recognized
    classes (model grounding + witness-emission faithfulness) — the
    lazy lfp is the grounded model of what SAW's mfix computes
    (§3.2a).
    CORRECTION (2026-07-16, self-caught same day): an earlier draft
    graded this certificate on the VERBATIM TRANSLATED BODY. That is
    ill-defined (the translated body is eager — it has no lazy
    Kleene chain), and the natural repair (elementwise
    characterization on pure inputs, then lazy lfp of that) is
    UNSOUND: source element `rec[i] * 0` behaves as the constant-zero
    operator on all pure inputs (total lazy lfp) while SAW's mfix
    forces rec[i] and DIVERGES. Pure-input behavior cannot see
    forcing structure; only the SOURCE term carries it. Hence the
    certificate carrier must be the emitted witness — which makes
    Phase B (witness pipeline incl. Haskell-side witness emission) a
    PREREQUISITE of the general tier, not an optional companion.
    This is also an independent re-derivation of the calculus rule:
    classification and certification must come from source shape,
    never from translated/emitted behavior.
  - Automation tier (syntactic): the recognizers become SUFFICIENT
    CONDITIONS discharging the general certificate mechanically
    (Phase A's A1 is literally "H_prod ⇒ lazy-lfp-total"). The
    recognizer stops being the expressiveness boundary and becomes
    an optimization; the iterate family stops being a hard reject —
    a user can hand-prove its certificate without a validated
    lowering. Recognizer bugs demote to wrong sufficiency claims,
    which are Lean theorems (Phase B), not Haskell trust surface.
* Binding riders: certificates stated against the verbatim wrapped
  body only (fifth-audit discipline); no evidence-as-hypothesis
  anywhere in the tier.
* Sequencing consequence: this re-ranks Phase A from verification
  nicety to the ENABLING ARTIFACT of the general tier — the
  certificate is not statable without the pointwise-lazy semantics
  in the library.
