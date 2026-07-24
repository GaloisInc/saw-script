# saw-core-lean status

Last updated: 2026-07-23 (0.02 census pass: BV native-eval tier
package complete, compositional replay chains, toolchain v4.32.0,
W2(d) hardening, docstring lint; plan:
`doc/2026-07-14_release-plan.md` §0.02)

## Purpose

`saw-core-lean` is a SAW proof backend. Its job is to translate SAWCore
terms, Cryptol-module definitions, and SAW proof obligations into Lean 4
source so Lean can discharge or check those obligations in its kernel.

Operationally, it fills the same slot as a solver backend in a SAW
workflow: SAW emits a verification condition, the backend presents that
condition to another trusted engine, and success means the obligation is
closed. The difference is that Lean checking is proof-kernel based, so
the emitted artifact should remain inspectable and replayable.

## Current Strategy

The active design is Phase beta, implemented by the position/callee
calculus (`doc/2026-07-02_position-callee-calculus.md`): value-domain
SAW expressions translate to Lean expressions at `Except String T`,
where `T` is the Lean translation of the SAW type; type-level
expressions translate raw. As of the position-directed translation
refactor (`doc/archive/2026-07-08_position-directed-translation-plan.md`,
Slices 0–7 complete), the calculus IS the implementation:

- Every translation is directed by a declared expected position
  (`ExpectedPosition`); callees carry declared argument-mode
  conventions (`ArgMode` tables); adaptation between representations
  happens at a single chokepoint (`adaptTo`) where forbidden
  adaptations are unrepresentable.
- Producers stamp `TranslatedTerm` production records (the produced
  shape); records are the translator's single source of truth, and
  demanded positions flow through explicit parameters/conventions
  rather than stored stamps (the write-only produced-at stamp was
  removed by the 2026-07-14 release audit). Shape is never re-derived
  from emitted Lean terms — that inspection class is deleted and a
  source lint in the smoketest keeps it deleted.
- Equality subjects classify by the operand-domain rule
  (`standaloneEqualitySubjectRep`); no surround declares a
  representation. `Eq.rec` transports run at a fully declared
  `EqRecConvention`.
- Recursors run at a declared `RecursorConvention` derived from the
  motive result position; every directly-emitted `@Foo.rec` carries a
  Lean-checked constructor-order assertion (`saw_ctor_order`), so a
  reordered Lean support inductive or a reordered SAWCore declaration
  fails the emitted file loudly.
- SAW `error` routes to `saw_throw_error`; `Prelude.fix` and partial
  operations route through proof-carrying obligations with
  Lean-checked evidence.
- `offline_lean` is EMISSION-ONLY (2026-07-14): it writes the goal
  file and returns `SolveUnknown`, so the goal stays unsolved on the
  SAW side and scripts wrap it in `fails`. SAW never claims a goal on
  the strength of an export. `offline_lean_replay` (LANDED
  2026-07-16, `doc/2026-07-16_replay-design.md`) is the discharge
  path: fresh in-process emission is the authority, the factored
  trust kernel (`saw-core-lean/replay/lean-check-core.sh`) enforces
  the exact-match axiom allowlist / placeholder policy / drift and
  closer probes, and success records `LeanReplayEvidence`. Pinned by
  `saw-boundary/offline_lean_export_only`,
  `workflows/replay_{e1,running_sum}_verify`, and
  `saw-boundary/replay_reject_{sorry,axiom,suffix_axiom}`. The LLVM
  `verifyObligations` loop runs every condition's tactic before
  failing, so multi-obligation `llvm_verify` still emits all files.

## Known State

Passing (the standing fences):

- Lean support library: `lake build` green on pinned toolchain
  `leanprover/lean4:v4.32.0` (bumped from v4.29.1 on 2026-07-23;
  drift across 340 proof rows was 2), including the
  `saw_ctor_order` positive/negative self-tests, the
  `saw_fix_bounded` / `atRuntimeCheckedM` / `saw_throw_error`
  `#guard_msgs` behavior fences, and the `linter.missingDocs`
  build option (all 153 public declarations documented 2026-07-23;
  a new undocumented declaration warns in `lake build`).
- `cabal test saw-core-lean-smoketest`: 74 tests, including the
  Slice 7 anti-regression source lint.
- `otherTests/saw-core-lean`: `make conformance` exit 0 — 235 rows
  in conformance scope (117 differential SAW-vs-Lean evaluation,
  91 obligation shape, 27 saw-boundary; recounted from disk
  2026-07-23 after the intmod boundary/rejection rows landed), with
  emitted artifacts elaborated. Tree restructured 2026-07-15 (see
  otherTests/saw-core-lean/README.md): `workflows/` split out of
  `drivers/` for the end-to-end SAWScript rows; `shape/` renamed
  (now `negative/`); the 17 legacy `drivers/conformance_*` litmus
  rows dispositioned (15 retired against named successors, 2 unique
  residuals migrated as `differential/vector_zip_unequal` and
  `differential/nat_division_defined`).
- Emitted-Lean byte-diff oracle: `.snapshots/op2-baseline`, re-cut
  2026-07-24 immediately after a fully green `make test` on the
  current binary — `support/emitted-lean-snapshot.sh diff
  .snapshots/op2-baseline` clean at 372 artifacts. Before the
  re-cut, every hunk of drift vs the previous (2026-07-16) baseline
  was accounted for by committed, suite-verified work: 18 CHANGED
  (the ten 2026-07-23 edge-case-matrix `observed.lean` rewrites +
  the eight chacha qround emissions from the 2026-07-22
  explicit-literal spec respelling) and 57 NEW (rows added during
  0.02). The 2026-07-16 baseline is retired REVERSIBLY to
  `.snapshots/superseded/op2-baseline-2026-07-16`. (History: the
  earlier "1267" count was a scan bug — the scan now excludes
  `.snapshots/` wholesale.)
- Driver + workflow rows (`bash test.sh` per-row,
  `lean-driver-test.sh`) green, including the ChaCha20 core verify
  workflow (explicit-literal spec spelling, Pattern 10) and the
  prelude auto-emit driver; full `make test` exit 0 on the
  restructured tree (58 gaps in full-suite inventory scope,
  census above).

Known-gap census (release 0.02 posture, taken 2026-07-23; +1 the
same day, see the audit note below): 54 pinned `.known-gap` rows in
conformance scope (differential 23 / obligations 18 /
saw-boundary 13), plus 3 `proof-gaps/` rows and the stretch probe
in the full-suite inventory — 58 total, the number `make test`
reports.

**2026-07-23 audit + edge-case-matrix addendum.** An independent
audit found a REAL soundness defect in the trusted support layer:
`bvToInt` was realized as the SIGNED conversion while SAW's is
UNSIGNED (Prelude.sawcore:2113; divergent on every sign-bit-set
input; the only test case, 0x7f, never crossed the sign bit). Fixed
same day (commit "SOUNDNESS FIX — bvToInt"), zero landed proofs
affected, and the differential row now pins the sign-crossing pair.
In response, the differential corpus gained a 200+-case labeled
edge-case matrix across ten rows (conversions, arithmetic,
division, shifts/bitwise, order/width/counts, Nat, Int, Int
div/mod, IntMod, Rational) — each case is its own SAW-vs-Lean
observation line, so a single divergent case names itself. The
matrix immediately caught a second fidelity item: SAW's concrete
evaluator CRASHES at `Z 0` (`toIntModOp` = Haskell `x mod 0`) while
the library totalizes — pinned as
`differential/intmod_zero_boundary` (the +1 census row); the
library's false "no-reduction convention" comment is corrected, and
the disposition was decided STRICT the same day (user decision):
translation now REJECTS `IntMod` at modulus 0 and at any
non-literal modulus (`saw-boundary/intmod_zero_rejection` pins both
diagnostics), so the total Lean realizations are unreachable at the
incoherent point. A
follow-up whole-surface fidelity review (independent reviewer,
every public library definition dispositioned against
Prelude.sawcore/Prims.hs/Concrete.hs) found NO further same-value
divergences and confirmed the classic risk sites (flipped
comparators, signed div/rem, floor div/mod, shift direction/fill,
lg2/width conventions, zip truncation, fold direction, iteM
laziness, unreduced-Rational observations) exactly faithful. Delta from
the 0.01 census (64 conformance-scope + 7 proof-gaps): 11
conformance rows un-gapped and 4 proof-gaps discharged across
0.02 — the Stream@core hole closed (kind-directed domain map,
2026-07-17), the transport-carrier convention landed (2026-07-19),
and the BV package tail completed under the two-tier trust policy
(salsa/chacha q_eq family, the 8 chacha-core qrounds via the
Pattern-10 spec spelling, `llvm_eq_u128`, `llvm_popcount_eq`, and
`llvm_doubleround_comp` — the first fully green compositional
replay chain, strict tier).

**0.02 exit-criterion statement**: no current known-gap row pins a
sound-but-undischargeable emission, modulo exactly the two
documented chacha observer-budget rows
(`differential/cryptol_chacha20_{iround_zero,core_iterate}` —
both translate, emit, and ELABORATE; the residual gap is that the
`#reduce` differential OBSERVATION of the 16x32 concrete
computation exceeds Lean's default recursion depth, and the
noncomputable emissions rule out `#eval`). Every other row is a
clean rejection, a SAW-side evaluator stub, or an
observation-path limitation, per the tiers below. The 3 surviving
`proof-gaps/` rows are the same two chacha shapes at the
proof-workflow level plus `llvm_doubleround_itp`, the preserved
direct-ITP attempt superseded by the compositional
`proofs/llvm_doubleround_comp` discharge.

Tiers:

1. **[ELIMINATED 2026-07-16, still true at the 0.02 census]** The
   sound-but-undischargeable wrapped-fix tier is gone: the OP-3
   successor landed (W1, R0-R4) — recognized fix classes lower to
   PROVEN realizations (running sum, popcount32, E6, rec_ones
   discharged end-to-end), everything else rejects loudly. See
   Known Holes below. The no-zip lookback-1 recurrence family
   (s20_hash's `zs` — boundary-pinned 2026-07-22 at
   `workflows/llvm_s20hash_comp`) rejects loudly; the recognizer
   extension is the scheduled 0.03 fragment-semantics program.
2. **Clean rejections** (named diagnostics, pinned boundary rows):
   iterate-family and paired-stream fixes, direct recursors
   (Nat/Pos/Z/Bool/Accessible*), user datatypes, proof-primitive
   realization families, SMT-array/enum/polynomial surfaces,
   raw-position `error`, residual `natCase`/`ZtoNat`/`scanl`/
   `expByNat`/ListSort surfaces.
3. **Workflow scope**: `offline_lean` is emission-only — SAW leaves
   punted goals unsolved and never claims them; discharge is
   `offline_lean_replay`. Remaining differential gaps are
   SAW-simulator `Unimplemented`/panic stubs and error-outcome
   observation paths (no executable SAW-vs-Lean error comparison),
   all pinned.

Bitvector automation trust policy (0.02, user decision 2026-07-21):
TWO-TIER. The strict tier admits exactly the kernel plus
propext/Classical.choice/Quot.sound and the two Vec/BitVec bridge
axioms; a per-row, loudly-labeled `native-eval` tier additionally
admits bv_decide's per-invocation proof-local native axioms
(`.trust-tier` markers; enforcement in `replay/axiom-audit.awk`,
both audit consumers, and the 30-case
`support/trust-tier-selftest.sh` mutation suite; migration trigger:
lean-smt kernel-checked BV reconstruction). Policy statement:
`doc/proof-cookbook.md` §"Bitvector automation trust policy".

Known holes, all loud or pinned:

- RESOLVED 2026-07-14 (release 0.01 decision): the former deliberate
  red pair `drivers/cryptol_chacha20_{core_iterate,iround_zero}` is
  reclassified to `saw-boundary/` as expected rejections pinning the
  named `Prelude::Stream@core` diagnostic (success goldens retired to
  git history). The translation path folds into the OP-3 successor
  design. The driver suite has no deliberately-red rows anymore.
- Direct recursors for Nat/Pos/Z/Bool/AccessibleNat/AccessiblePos are
  gated with specific diagnostics (constructor order / representation
  mismatches); the design for lifting the gate is
  `doc/archive/2026-07-03_direct-recursor-semantics-design.md` (PosRep
  inductive + source-shaped checked realizations), tracked separately.
- User-datatype recursors and datatype auto-emission reject with
  diagnostics (pinned by `saw-boundary/user_datatype_rejection`).
- RESOLVED 2026-07-14 (both formerly-filed loud gaps): top-level
  `write_lean_term` annotates from the produced body's production
  record (pinned `obligations/write_term_runtime_nat`); pair carriers
  at a Prop component reject with a named diagnostic (pinned
  `saw-boundary/pair_prop_component_rejection`).
- RESOLVED 2026-07-14 (audited,
  `doc/2026-07-14_reachable-raw-error-disposition.md`): the
  `h_raw_error_ : False` contract is retired. Function-typed
  `Prelude.error` with a value-domain result lowers to the
  constant-error function (message preserved; polynomial t1 now
  elaborates sorry-free); all other raw-position error rejects with
  a named diagnostic (pinned `saw-boundary/raw_error_rejection`).
- CLOSED 2026-07-16 (W1, slices R0-R4 — commits 93fb03617 through
  d3aa53199; was: filed 2026-07-12, `saw_fix_unique_exists`
  unsatisfiable for every strict wrapped fix body): the OP-3
  successor program landed end-to-end. Wrapped fixes are TWO-STATE:
  recognized classes lower to PROVEN realizations (Class F
  `saw_fix_bounded_choose` — running_sum, popcount32, E6, module
  popcount discharged; Class S-single `saw_stream_realize` —
  rec_ones discharged), everything else rejects with a named
  diagnostic carrying the recognizer's reason. The wrapped
  `saw_fix_unique_exists` contract is DELETED (raw variant retained
  per Instance 3, census-checked); the sound-but-undischargeable
  wrapped-fix tier is ELIMINATED. Paired streams (stream_fibs) and
  the iterate family (stream_step) are pinned boundary rejections;
  the Bool divergence witness is pinned at
  `saw-boundary/fix_obligation` and can never emit again. Six seam
  bugs were found and fixed across the arc — all by audit/review
  before any emission depended on them; the recognizer surface is
  FROZEN (growth requires the fragment reference semantics first —
  see doc/2026-07-16_fragment-semantics-scoping.md and the
  sixth-audit record in the successor design doc).
- RESOLVED 2026-07-12 by Slice OP-2 (was: eta-expanded checked-access
  wrappers fabricated unprovable `η < n` evidence): evidence-less
  positions now route through `atRuntimeCheckedM`, and the
  saw-lean-example invol/eq_spec goals discharge.
- Shipped 2026-07-12 (Slice OP-1): emitted evidence chains gained the
  checked `assumption | omega | normalize; omega` step (plus `rfl` for
  unsafeAssert and the div/mod bridging lemmas); nine differential
  known-gap rows un-gapped into true coverage (census 77→68). The
  surviving `sorry`-pinned rows expose two named surfaces for OP-2:
  guard-dependent `iteM (ltNat i k)` branch bounds emitted without the
  guard as evidence, and value-dependent bounds over runtime Nats
  (details in the design doc's OP-1 implementation record).
- Shipped 2026-07-12 (Slice OP-2, second Opus audit folded in):
  evidence-less `at` positions lower through `atRuntimeCheckedM`
  (Prelude-exact error semantics) decided by interval entailment over
  the binder bounds environment; interval-entailed slots keep the
  proof-carrying form. Four more rows un-gapped (census 68→64), and
  the saw-lean-example invol/eq_spec goals now discharge end-to-end
  from raw emitted artifacts — the eta-wrapper hole is closed.
- RESOLVED 2026-07-19 (was: filed 2026-07-12, whole-module
  translation of polymorphic indexing comprehensions rejected at
  `Prelude::Either@core`): the Stream@core hole closed 2026-07-17
  (kind-directed domain map) and the function-carrier transport
  mismatch closed 2026-07-19 (mode-uniform type-subject spine
  convention, `doc/2026-07-18_transport-carrier-design.md`). The
  demo's REDUCED rev.cry module now translates and elaborates
  un-`fails`-wrapped (`examples/saw-lean/out/Rev.lean`); the interim
  `saw-boundary/polymorphic_seq_module_rejection` pin was retired
  with the fix. Only the FULL module still rejects — at raw-position
  `Prelude.error`, a different (intended) boundary.
- Two Vec/BitVec round-trip axioms remain in the support library TCB
  (cheap, separately tracked proof task).

## Next Work

Release 0.02 posture (`doc/2026-07-14_release-plan.md` §0.02;
detailed punch list in TODO.md):

1. [DONE through 2026-07-23] W1 (OP-3 successor, R0-R4), W2(a) BV
   package under the two-tier trust policy, W2(b) `llvm_eq_u128`,
   W2(d) hardening (helper goldens + `#guard_msgs` fences),
   `offline_lean_replay` + compositional replay chains, docstring
   pass, toolchain v4.32.0.
2. Scheduled 0.03: the fragment-semantics program
   (`doc/2026-07-16_fragment-semantics-scoping.md` Phases A-C) and
   the no-zip lookback-1 recognizer extension it gates — unlocks
   the s20_hash compositional rung and the chacha iterate family
   (user decision 2026-07-22).
3. The direct-recursor / `PosRep` program
   (`doc/archive/2026-07-03_direct-recursor-semantics-design.md`) — now
   tractable on the position-driven recursor convention.
4. Universe-generalized pair/record carriers (would lift the
   pair-at-Prop rejection), proof-primitive realization families,
   user datatypes — example-driven coverage.
5. Pre-release gate: the whole-project multi-reviewer skeptical
   soundness review (TODO.md release gate) and the recorded replay
   hardening follow-ups (CI-harness rebase onto the factored
   checker; binder-type telescope comparison). [Cabal data-files
   relocatable packaging: DONE 2026-07-23 — assets ship as package
   data; `SAW_LEAN_ROOT` is now an optional dev override.]
