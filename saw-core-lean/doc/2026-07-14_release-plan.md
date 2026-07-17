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
  TODO.md hard requirements). The committed 0.02 plan is the
  section at the end of this doc.

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
   1. **Mixed-solver flagship — DONE 2026-07-15.**
      `workflows/llvm_point_verify` is the complete story: w4
      verifies point_eq/point_new/point_copy and point_add
      compositionally through all three VERIFIED overrides, while
      the same point_eq obligation is punted to Lean and its
      kernel-checked discharge is green (`proofs/llvm_point_eq`,
      sorry-free, axiom-audited). `workflows/llvm_salsa20_q_verify`
      is the second mixed row (w4 qround + rowround composition;
      Lean punt gap-tracked under the BV policy). Direction note:
      SMT-verified-callee → Lean-punted-caller composition works in
      0.01; the reverse needs 0.02 replay.
   2. **Wide-bitvector algebraic property — SATISFIED BY PROMOTION.**
      `proofs/E7_wide_assoc` already discharges 256-bit addition
      associativity via named lemmas under the trust policy (no
      `bv_decide`); the release narrative should feature it. (The
      BV-policy proof-gaps remain the harder shape: quarterround's
      mixed rotate/xor/add equations, plus the newly characterized
      `proof-gaps/llvm_eq_u128` memory-model tower with its two
      named missing-lemma families.)
   3. **Memory-safety exercise port — DONE 2026-07-15.**
      `workflows/llvm_swap_verify` (Case Study F, completing the
      optional ladder rung): mixed-solver row over the swap/
      selection_sort exercise whose Lean-punted goal is a Crucible
      SAFETY ASSERTION (the swap-store bounds check) — a new goal
      flavor for the corpus — discharged sorry-free via the
      completed-outline mechanism (`proofs/llvm_swap_eq`, drift
      check + axiom audit green).
   4. **Sequence-surgery property — DONE 2026-07-15, with a
      coverage finding.** `workflows/cryptol_seq_surgery`: four
      SAWCore-direct proof-carrying goals routing ALL FOUR
      zero-coverage checked helpers (upd/slice/gen/updSlice
      WithProof_checkedM), each discharged sorry-free via the
      completed-outline mechanism
      (`proofs/cryptol_seq_surgery_{upd,slice,gen,updslice}`).
      FINDING: the *WithProof helpers are UNREACHABLE from Cryptol
      surface syntax — `update`/`take`/`drop` unfold to gen+at+ite
      before translation, so only `at` gets a checked contract;
      the helpers' zero coverage was structural. Whether Cryptol
      surface ops should someday route to the WithProof family is
      a recorded 0.02+ design question, not assumed.
   5. **`Z n` / `IntMod` arithmetic property — DONE 2026-07-15.**
      `workflows/cryptol_zn_arith`: three `Z 7` properties
      (add-commutativity, mul-commutativity, add/neg cancellation)
      emitted and each discharged sorry-free
      (`proofs/cryptol_zn_{add_comm,mul_comm,neg_cancel}` — targeted
      `simp only` through the reducible `Int.fmod` realizations plus
      the core `Int` lemmas; axiom audits clean). First end-to-end
      workflow coverage of the IntMod surface.
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


---

## 0.02 plan (committed 2026-07-15, user-confirmed)

Story: cover all our examples in a reasonable way, and close every
gap that can reasonably be closed. Three workstreams; W1 leads.

**W1 — Recurrence/stream program (the headline).** OP-3 successor
design against the third audit's six minimum conditions → fourth
independent audit → implementation. Acceptance ladder:
`proof-gaps/cryptol_running_sum_verify` → `offline_lean_popcount32` +
E6 → `llvm_popcount_eq` → the `rec_ones`/`stream_fibs` module rows →
the Stream@core/Either@core translation path (un-parks the boundary
rejections) → `rev.cry` whole-module translation works and the demo
loses its `fails`-wrapped step 3. Closes 5 of the 9 proof-gaps, two
boundary families, and the demo's visible limitation.

**W2 — Proof-support library.** (a) A policy-compliant BV proof
strategy for the quarterround equation class — unparks
`llvm_salsa20_q_eq`, `llvm_chacha20_q_eq`, and chacha20-core's eight
obligations at once. The `bv_decide` trust policy HOLDS for 0.02
(decision 2026-07-15); revisit only if the lemma route proves
genuinely intractable, as its own recorded decision. (b) The
`llvm_eq_u128` unlock: emitted-shape reduction lemmas for the
`genWithBoundsM`/`foldrM`/`atWithProof_checkedM` byte-loop towers,
plus the byte-to-word `bvEq` decomposition bridge (memory-model
examples generally need both). (c) Starter-tactic ergonomics for the
concrete-vector/rational nonzero differential gaps. (d) The deferred
hardening: realization theorems for the checked vector helpers,
goldens for the 11 zero-coverage emitter-wired helpers, and
`#guard_msgs` fences for `atRuntimeCheckedM`/`saw_throw_error`.

**W3 — Example breadth + replay (the product story).**
(a) Early/cheap: slate items 3-5 (memory-safety port,
sequence-surgery via the checked helpers, `Z n`/IntMod) plus the
coverage-matrix extras (fixed-bound C loop, Int workflow, signed-BV
property). (b) `offline_lean_replay` IS IN 0.02 (decision
2026-07-15): SAW invokes the pinned Lean toolchain on the exact
emitted obligation + completed proof, admits only on a kernel-checked
theorem of that exact type with no forbidden escape hatches — lands
mid-cycle, after W1 stabilizes obligation shapes; flips
`saw-boundary/offline_lean_export_only` into the replay-semantics
row and unlocks the Lean-verified-callee composition direction.
(c) Direct recursors via the PosRep design
(`doc/2026-07-03_direct-recursor-semantics-design.md`). (d) The
proof-primitive realization families as a mechanical batch.

**OUT of 0.02 (recorded):** simulator `Unimplemented` differential
gaps (blocked on SAW's evaluator upstream — not ours to close); user
datatypes and SMT-array semantics (each needs its own design cycle;
0.03 candidates unless an example forces one earlier);
JVM/MIR backends; SHA512-at-scale; the lean-smt track (case rungs
G/H); pair-at-Prop universe generalization (stays a rejection until
an example hits it).

**0.02 exit criteria:** `rev.cry` demo step 3 produces `Rev.lean`;
`running_sum`, `popcount32`, and E6 discharge sorry-free; the
quarterround gap family unparked (or explicitly re-parked with a new
recorded reason); replay landed with the export-only row flipped;
the workflow-accounting invariant maintained (every workflow row's
Lean side discharged or precisely gap-documented); known-gap census
delta stated in STATUS.md (target: the sound-but-undischargeable
tier eliminated).


## In-ITP decomposition pattern (wave-3 pilot result, 2026-07-16)

`workflows/llvm_rowround_itp` + `proofs/llvm_rowround_itp`: salsa20's
rowround verified with an EMPTY override list — SAW inlines all four
quarterround calls into one 2695-line goal — and composed INSIDE
Lean. Structural finding: SAW inlines quarterround on BOTH sides, so
the honest override granularity is the ROTATE (`rotl_shlor_32`:
C's shift-or form = spec's `rotateL`, proved via
`BitVec.rotateLeft_def`), applied at all 16 sites; the two sides are
then spec-vs-spec and the quarterround BV wall NEVER APPEARS — you
never prove quarterround correct, only that C-inlining equals the
spec's normal form. Method: staged rewriting (sequence-literal
scaffolding → fold-to-16-per-word-goals → per-word BitVec push +
`ac_rfl`; monolithic simp blows heartbeats, per-word is bounded).
Extension: columnround is a near-copy; doubleround (~5K lines) is
the first two-level test. NOTE the pattern's relation to the
BV-policy gaps: it does NOT unpark them (standalone quarterround
correctness still needs the W2 strategy) but shows compositional
verification can route AROUND that wall entirely.

**Extension result (2026-07-15, commits `9cecda1e2`/`42fa23783`):**
columnround transferred verbatim (lemma library byte-identical to the
rowround row; permutation invariance confirmed) — GREEN in
`proofs/llvm_columnround_itp`. doubleround's two-level discharge is
COMPLETE and axiom-clean but its tactic cost (core `simp` reduction +
16 double-depth per-word `ac_rfl` closes, ~130-210 s across runs)
does not robustly fit the harness's 120 s per-process cap; it lands
as `proof-gaps/llvm_doubleround_itp` with the measured scaling law.
Depth verdict: the OUTER composition is depth-invariant; the
per-word arithmetic closes scale with inlined term size and cross
the CI wall-clock cap at depth 2. Principled unlock (recorded in the
GAP.md): split the monolithic obligation so the 16 per-word closes
elaborate as independently-budgeted lemmas — packaging, not new
mathematics. Independently re-verified end-to-end at
`LAKE_TIMEOUT_SECS=500`: harness exit 0, checked theorem audit
passed.

## De-scoping decision (2026-07-16)

W1-minimal close: finish R3b flip + R4 retirement (two states for
wrapped fixes: proven realization or loud reject — nothing else), plus
ONE bounded differential batch (bvUExt/bvSExt, boolean ops, Int
comparisons — the census's value-carrying exposures). The fragment
semantics program (Phase A/B/C, certificate tier, lux) is FROZEN as a
scoping record with named revisit triggers; the zone anatomy /
grounding record / census are documentation artifacts owing no
follow-through. Then 0.02 proper resumes (replay, example breadth).
