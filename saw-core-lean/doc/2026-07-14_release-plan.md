# Release plan: 0.01 (coherence) and 0.02 (coverage)

**Date**: 2026-07-14. **Status**: ACTIVE — this is the operative
release plan; TODO.md's per-item tracking remains authoritative for
execution detail.

## Release philosophy

The backend's soundness story is already release-shaped: every
translation either emits Lean that elaborates with explicit proof
obligations, or fails at SAW translation with a named diagnostic;
SAW never claims an undischarged goal; the trusted base is the two
documented Vec/BitVec round-trip axioms plus Lean's kernel. What a
release adds is *coherence*: the fences all green on a clean
checkout, the docs matching the repo, the parked decisions decided,
and the known limitations stated in one place.

- **0.01 — coherence.** A sound, honest proof-discharge prototype
  for the current fragment. `write_lean_term` and `offline_lean`
  work end-to-end (saw-lean-example invol/eq discharge from raw
  artifacts); everything out-of-fragment rejects loudly with a
  pinned diagnostic. `offline_lean` is scoped as emit-stage
  evidence: SAW-side replay remains the deferred Priority-5
  product-soundness boundary and 0.01's docs must say so plainly.
- **0.02 — coverage.** Driven by pushing examples through the
  position/callee calculus: the design's own contract is that new
  coverage means new declared conventions/contract-table entries
  plus Lean support lemmas, not translator re-architecture (a new
  example that requires emission changes is a coverage bug — see
  TODO.md hard requirements). Spine, in value order: the OP-3
  successor design (recurrence class), the Stream@core/Either@core
  recursor-convention work it drags along (un-parks whole-module
  translation including rev.cry), direct recursors (PosRep),
  proof-primitive realization families. SAW-side replay lands when
  sequencing favors product soundness over coverage.

## Decisions recorded (2026-07-14, user-confirmed)

1. **Stream@core pair ships as expected rejection.**
   `drivers/cryptol_chacha20_{core_iterate,iround_zero}` migrate
   from deliberately-red drivers (goldens expecting successful
   translation) to expected-rejection rows pinning the named
   `Prelude::Stream@core` diagnostic. The related
   `Prelude::Either@core` polymorphic-comprehension rejection stays
   a pinned boundary
   (`saw-boundary/polymorphic_seq_module_rejection`). The
   translation path (the May parametric-bridge family / lazy
   selection) folds into the OP-3 successor design post-release.
2. **OP-3 ships as the documented top limitation.** The wrapped-fix
   recurrence class (running-sum, popcount, rec_ones, stream_fibs,
   ChaCha20-iterate) emits obligations that are sound but
   undischargeable (`saw_fix_unique_exists` is unsatisfiable for
   strict bodies — errors are always fixed points). SAW never
   claims these goals, so shipping is sound; the audit-gated
   successor design (six minimum conditions,
   `2026-07-12_op3-structural-fix-design.md`) continues after 0.01.

## 0.01 workstreams

In execution order (TODO.md tracks per-item state):

1. **Hygiene found by the 2026-07-14 grounding review:**
   - Finish the half-authored
     `saw-boundary/offline_lean_export_only` row (untracked
     leftovers currently break `make conformance` exit-0). The row
     is worth having: it pins that `offline_lean` must not act as
     an admitting exporter — a false goal leaves SAW reporting
     unsolved subgoals.
   - Re-cut the emitted-Lean snapshot baseline (op1-baseline was
     never re-cut after Slice OP-2; 32 artifacts differ, all
     verified to be the OP-2 `atRuntimeCheckedM` migration shape;
     driver goldens were refreshed, only the oracle baseline is
     stale). Sync STATUS.md's oracle line.
2. **Emission-only `offline_lean` (user-directed scope addition,
   LANDED 2026-07-14).** The tactic previously ADMITTED the goal on
   mere emission (`SolveSuccess` with `SolverEvidence`) — an
   admitting exporter, the worst 0.01 product-soundness rough edge.
   Now: `offline_lean` returns `SolveUnknown` (goal stays unsolved;
   scripts wrap in `fails`); `offline_lean_replay` is registered but
   fails with a named diagnostic reserving the 0.02 replay
   interface; the LLVM `verifyObligations` loop runs every
   condition's tactic before failing so multi-obligation
   `llvm_verify` still emits all files in one pass. Ten driver rows
   + demo.saw updated and green; new boundary pins
   `offline_lean_export_only` (false goal leaves SAW unfinished
   while emitting) and `offline_lean_replay_disabled`. offline_rocq
   deliberately keeps its legacy admitting semantics.
3. **Stream@core reclassification** per decision 1; full driver
   suite green afterward.
4. **OP-2 tail (the genuinely mid-stream items):**
   - Rider audit: every in-corpus `h_raw_error_ : False` position
     verified genuinely unreachable-with-context.
   - Reachable-raw-error disposition design note (audit-first),
     then implementation if the decision is "reject".
5. **The two filed loud emission gaps** (small, clear fixes):
   - `write_lean_term` of a runtime-computed Nat: annotate from the
     produced term's recorded shape, not a bare type translation.
   - `PairValue` at a Prop instantiation: reject loudly or
     universe-generalize; pin either way.
6. **Release fence sweep + rough-edge cleanup:** full
   `bash test.sh test` (all categories incl. drivers) green on a
   clean checkout; smoketest; lake build; conformance exit 0; demo
   `make invol eq`; docs pass (STATUS.md, saw-lean-example README,
   CONFORMANCE.md inventory) with the 0.01 limitation statement in
   one place.

7. **Worked-example slate (added 2026-07-15, user-directed):** show
   that real SAWScript proofs usefully discharge through the Lean
   backend — examples framed as verification workflows, not harness
   fixtures. Precondition (DONE 2026-07-15): the existing corpus is
   in honest state — 33 live discharging rows, 7 pinned proof-gaps
   with accurate GAP.md notes (5 recurrence-class, 2 BV-trust-
   policy), no dead pointers. The slate, in release-narrative order:
   1. **Mixed-solver flagship**: one `llvm_verify` script where most
      obligations close via SMT (`w4`) and one hard goal is punted
      to `offline_lean` and discharged in Lean — the honest 0.1
      product story ("Lean where SMT struggles, SMT elsewhere, one
      script"). No current row shows the mixed workflow.
   2. **Wide-bitvector algebraic property** (`[256]`+/`[384]`):
      painful for bit-blasting, closed in Lean by named lemmas
      under the trust policy (no `bv_decide`). Doubles as progress
      toward unparking the two BV-policy proof-gaps
      (`llvm_{chacha20,salsa20}_q_eq`).
   3. **Memory-safety exercise port** (from `exercises/
      memory-safety`): a points-to goal through `offline_lean`,
      discharged — the Crucible→Lean path on teaching material.
   4. **Sequence-surgery property** (`update`/`slice` round-trip):
      deliberately routes the `updWithProof_checkedM`/
      `sliceWithProof_checkedM` family, closing part of the
      zero-coverage-helper gap as a side effect.
   5. **`Z n` / `IntMod` arithmetic property**: end-to-end coverage
      for a surface that has emitter wiring but no worked example.
   Definition of done per example: `.saw` script (emission-only,
   `fails`-wrapped), emitted artifact elaborates, `proof.lean`
   discharges sorry-free under the axiom policy, wired as a
   `proofs/` (or driver+proofs) row, plus a short section in a
   worked-examples doc. An example that hits a coverage bug gets
   pinned per the hard requirement and becomes named 0.02 backlog;
   one that hits a documented rejection maps the fragment edge and
   is reported as such.

Explicitly NOT in 0.01: OP-3 implementation, Stream/Either
translation paths, direct-recursor PosRep work, proof-primitive
realizations, user datatypes, SAW-side `offline_lean` replay,
SHA512 stretch. All tracked for 0.02+ in TODO.md.

Slate sequencing default: item 1 (the mixed-solver flagship) is the
minimum release bar for the "usefully discharges SAWScript proofs"
claim; items 2–5 land as they succeed and roll into 0.02 backlog
otherwise.

## 0.01 exit criteria

- Clean checkout: `cabal test saw-core-lean-smoketest`,
  `lake build`, `make conformance` (exit 0), full `bash test.sh
  test` (exit 0, no deliberately-red rows), demo `make invol eq`
  all green.
- Snapshot oracle clean against the freshly cut baseline.
- Zero unexplained diffs between docs and repo (STATUS.md Known
  State is literally true).
- Known-gap census stated in STATUS.md with the tier breakdown
  (sound-but-undischargeable / clean rejections / workflow scope).
  [DONE 2026-07-15.]
- Worked-example slate: at least the mixed-solver flagship
  discharged end-to-end (workstream 7); remaining slate items
  landed or explicitly rolled to 0.02.
