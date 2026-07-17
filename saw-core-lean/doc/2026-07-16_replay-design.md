# offline_lean_replay design (0.02-W3; audit-first, pre-implementation)

**Date**: 2026-07-16. **Status**: DRAFT for adversarial audit before
any implementation (house rule; this is the highest product-soundness
surface in 0.02 — replay is the switch by which SAW ADMITS a goal on
Lean's authority; the 0.01 admitting-exporter bug lived exactly here).

## Contract

`offline_lean_replay proof_dir : ProofScript ()` — admits the current
goal iff a user-supplied Lean discharge kernel-checks against the
goal SAW emits, under the same checker the test suite trusts.

## Design spine: ONE checker, productized

`support/lean-proof-test.sh` already implements the entire trust
kernel (staging, completed-outline drift check with the per-def
module form and the no-vacuous-#check assertion, elaboration, named
closer requirement, sorry scan, axiom audit against the fixed
allowlist). Replay MUST NOT reimplement it: factor the check core
into a shared entry point invoked by BOTH the CI harness and the
SAW-side replay. A second checker would drift; the single-checker
principle is this design's load-bearing decision.

## Flow

1. **Fresh emission is the authority.** Replay re-emits the goal
   in-process (writeLeanProp to a private staging dir). The user's
   copy of the emitted artifact is never trusted; artifact-swap is
   defeated by construction. If the user's proof was written against
   a stale emission, the drift/elaboration checks fail loudly.
2. **Staging**: user's `proof.lean` (+ optional `completed.lean`,
   the completed-outline mechanism, verbatim harness semantics).
3. **Checks** (all-or-nothing; any failure = ProofScript `fail` with
   the named check — never a silent SolveUnknown):
   a. completed-outline drift (if present): defeq-by-rfl against the
      fresh emission; per-def form for module artifacts;
      no-vacuous-#check assertion (R3b review finding F2's fix).
   b. `proof.lean` elaborates against the staged emission with
      LEAN_PATH pinned to {staging dir, repo support library} only —
      no import shadowing surface.
   c. Named closer of the goal's exact type (the harness's
      goal_closed contract).
   d. Sorry scan: zero tokens in proof.lean/completed.lean.
   e. **Axiom audit — the decisive gate**: #print axioms on every
      named closer; allowlist = propext, Classical.choice,
      Quot.sound, vecToBitVec_bitVecToVec, bitVecToVec_vecToBitVec.
      SIXTH-AUDIT WRINKLE RESOLVED HERE: emitted goals may carry
      sanctioned `by sorry` obligation placeholders in their TYPE; a
      discharge that leaves any placeholder LIVE depends on sorryAx,
      which the audit rejects — so "defeq modulo placeholder fill"
      needs no special mechanism. Either the completed outline
      replaced the placeholder with a real proof (proof irrelevance
      keeps the goal defeq), or the closer's axiom set betrays it.
4. **Evidence**: `SolveSuccess` with a new `LeanEvidence` record:
   goal hash, proof-file hashes, lean-toolchain version, support-
   library commit/hash, closer axiom list, wall time. Printed in the
   proof summary so a replayed admission is visibly Lean-backed.
5. **Trust delta** (catalog entry required at landing): replayed
   goals add Lean's kernel + the pinned toolchain + the staged
   support library to the TCB for that goal. Nothing else changes;
   offline_lean stays emission-only.

## Boundary rows to land WITH the slice (reject pins)

replay-green (an existing discharged row replayed end-to-end);
replay rejects: sorry in proof; wrong-type closer; new-axiom
smuggling; import-shadowing attempt; stale-emission drift; vacuous
module check. Each a named-diagnostic pin, same discipline as the
fix-program boundaries.

## Non-goals

No in-process Lean linking (subprocess `lake env lean` with the
pinned toolchain, matching CI); no acceptance of pre-built oleans;
no per-goal axiom-allowlist extensions (policy changes are design-
doc events, not call-site options).

## Open questions for the auditor

1. Is fresh-emission identity sufficient against all swap attacks,
   or must the staged emission ALSO be content-hashed into the
   evidence to guard the window between check and admission?
2. The factored checker runs under SAW's environment: does anything
   in the harness rely on CI-only invariants (cwd layout, elan
   state) that the product path must pin differently?
3. Determinism: emission is deterministic given (goal, library) —
   confirmed by the snapshot oracle discipline — but is goal-NAME
   generation (goalType/goalNum) stable enough to key the staging,
   or should replay ignore names and stage a single goal per call?

## Seventh-audit record (2026-07-16) — BINDING AMENDMENTS, do not implement as written

Verdict: spine sound (fresh re-emission authority; one factored
checker; axiom audit decisive). The central #print-axioms claim is
CONFIRMED airtight for in-statement placeholders (CollectAxioms
traverses types AND values of every reachable constant; proof
irrelevance does not prune the syntactic sorryAx reference in the
goal's statement value). Four amendments:

1. **(Load-bearing — goal-formation amplification.)** Replay
   converts emission bugs into FALSE SAW THEOREMS: today an emission
   bug yields a file nobody admits on; under replay an honest Lean
   proof of a mis-formed (weakened/trivialized) goal kernel-checks
   and SAW records it. The trust delta MUST add the emission
   pipeline (propToTerm, scPiList free-var abstraction,
   scNormalizeForLean) to the replayed-goal TCB, and the slice lands
   two cheap pins on every freshly-emitted goal: anti-trivialization
   (reject if the goal closes by trivial/rfl alone) and a
   Pi-telescope sanity check (binder arity/types match the sequent's
   symbolic inputs).
2. **(Env re-pinning; contains the real import-shadowing hole.)**
   The harness APPENDS ambient LEAN_PATH (a CI-clean-env assumption)
   — the factored core must CLEAR it; absolute project root; private
   per-call temp staging (never in-tree intTestsProbe, no lake-lock
   contention with user builds); timeout guard non-degradable (the
   CI wrapper silently drops it without coreutils). "Verbatim
   harness semantics" is unachievable; re-pin env explicitly.
3. **(Placeholder-location invariant.)** The axiom gate sees a
   placeholder ONLY when it is a subterm of the goal's statement
   value (the R2/R3b construction). A sibling-declaration
   placeholder (the raw-emit goal_holds stub) is invisible to
   #print axioms on the closer — guarded today only by the text
   scan. Replay asserts placeholder-is-load-bearing on the fresh
   emission; a future emission that factors an obligation into a
   sibling reopens the gap otherwise.
4. **(Evidence semantics.)** LeanEvidence is a NON-RE-CHECKABLE
   trust token (checkEvidence cannot re-run Lean; hashes are
   documentation, not verification — same status as
   SolverEvidence, unlike ProofTerm; catalog this). Define its
   checkEvidence case and a distinct TheoremSummary constructor
   with absorbing monoid behavior so mixed Lean/SMT proofs surface
   the Lean-backed dependency.

Adopted from open questions: single-goal-per-call staging (goalNum
instability is ergonomic, not soundness — fresh re-emission makes
stale keys fail loudly). Reject-row set extended: ambient-LEAN_PATH
shadowing, native_decide closer (Lean.ofReduceBool — allowlist
catches, row pins), timeout-must-fail (even degraded), goal-name
rebind, closer-routes-through-goal_holds-stub. Non-issues analyzed
and recorded: injected-but-unused axioms in completed.lean (inert;
rfl drift unfoolable), unicode homoglyphs (sorry is an ASCII
keyword; homoglyph axioms are off-allowlist; homoglyph closers fail
resolution loudly).
