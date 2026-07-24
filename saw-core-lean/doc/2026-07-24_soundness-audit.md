# Pre-release soundness audit — saw-core-lean

**Date:** 2026-07-24. **Status:** COMPLETE — findings reported; the
CRITICAL finding (R-1) and DOC-1 are FIXED (same day, see the FIXED
notes in place); the remaining findings are open and tracked in the
sequencing section.

**Method:** whole-project soundness review by a panel of six
independent reviewers (Opus-class, fresh contexts, none the
implementing session), each assigned a distinct part of the trust
chain and tasked with searching for unsound-acceptance paths — inputs
where SAW admits a goal whose checked Lean statement is false or has
different semantics. Shared charter: `.tmp/audit-goal.md` (the
calibrated reviewer prompt; framed as compiler-correctness review, not
attack tooling). Working assumption: a defect exists until the surface
is shown sound. This is the release-gate review tracked in TODO.md,
and the direct successor to `2026-07-21_soundness-review.md` (three
surfaces, found the F1 lint bug) and `2026-07-23_fidelity-review.md`
(library realizations, found the bvToInt/IntMod class).

**Lanes:** (1) translator emission seams; (2) Lean trust base +
obligation contracts; (3) replay trust kernel; (4) two-tier trust
machinery; (5) test-harness vacuity; (6) SAW-side inputs +
integration seams + docs-honesty.

## Verdict

ONE CRITICAL soundness defect, confirmed end-to-end with a working
witness (**R-1** — the replay checker admits a goal on a proof of
`True`). It is a single, specific, fixable gate defect, not systemic:
every other lane cleared its core question and the surrounding
defenses hold (the two-axiom base, the axiom allowlist, the source
lint, the `sorry`/placeholder invariant, the tier machinery, and the
emitter's partial-op gating were each pressure-tested and stood). The
remaining findings are latent (not reachable today) or
housekeeping-grade.

**R-1 must be fixed before release** — while it stands, the backend's
central guarantee (SAW admits a Lean-discharged goal only when the
Lean proof actually proves the emitted obligation) is broken on the
completed-outline replay path.

## Severity summary

| ID | Sev | Lane | One line | Reachable today? |
|----|-----|------|----------|------------------|
| R-1 | **CRITICAL** | replay | completed.lean admits goal on a proof of `True`; real obligation never checked | **FIXED 2026-07-24** (was: YES — runtime replay driver + CI harness) |
| LB-1 | Medium | lean-base | raw fix contract `saw_fix_unique_exists_raw` is extensional-only; provable while SAW diverges | Latent (0 corpus uses; gated only by Haskell recognizer routing + a comment) |
| V-H1 | Medium | vacuity | negative-probe harness accepts ANY error; no expected-diagnostic pin | Latent (guards against future regression) |
| V-H2 | Low-Med | vacuity | obligation rows with only `absent:` directives pass on empty emission | Latent |
| V-H3 | Low | vacuity | obligation-observer error regex is dead (can't cross `:line:col:`) | Latent (masked by exit-code check) |
| LB-2 | Low | lean-base | `missingDocs` documented as "enforced" but only warns; harness checks exit code only | Live (doc/enforcement gap, not soundness) |
| TIER-1 | Low | tier/replay | replay is always strict-tier (ignores `.trust-tier`); safe asymmetry, undocumented | **FIXED 2026-07-24** (documented in residual-trust §3.2b; no code change — the strict direction is deliberate) |
| SEAMS-D3 | Low (unconfirmed) | seams | type-translation injectivity: type-image `Eq` obligation could be weaker if translation collapses two SAW-distinct types | Unknown (no witness; not proven either way) |
| DOC-1 | Tertiary | docs | self-test "27 cases" (proof-cookbook.md:309) — actually 30 | **FIXED 2026-07-24** (now says 32 — the R-1 fix added two cases) |

---

## R-1 (CRITICAL) — replay admits a goal on a proof of `True`

**Confidence:** HIGH — confirmed end-to-end through the real
`lean-check-core.sh` on v4.32.0: CHECK-OK, exit 0, `offline_lean_replay`
returned `SolveSuccess` ("Lean kernel check passed"), while the actual
obligation was never proved.

**FIXED (2026-07-24, immediately post-audit).** All four parts of the
recommended fix landed in both consumers, red-before/green-after:
goal-presence derives from the authority (`Generated.lean` in the
kernel, the tracked `.lean.good` reference in the CI harness); a
completed outline without a bare `def goal :` hard-fails
(`CHECK-FAIL: completed-outline-missing-goal-def`, plus
`authority-missing-goal-def` for a goal-less staged reference); the
goal-less per-def drift branch is REMOVED from the trust kernel (its
doubled-namespace probe was the capture surface); user files
mentioning `GeneratedHarness` are rejected
(`harness-namespace-in-user-file`). Regression pins:
`saw-boundary/replay_reject_unbound_completed` (the audit witness
end-to-end through SAW — confirmed CHECK-OK/`SolveSuccess` before the
fix, pinned rejection after) and two new `trust-tier-selftest.sh`
cases (goal-less completed outline; harness-namespace capture).
Positive rows re-verified: `replay_e1_verify`,
`replay_running_sum_verify`, `proofs/cryptol_running_sum_verify`,
`proofs/cryptol_module_rec_ones` (module-artifact per-def path,
CI-harness only, unchanged). Amendment recorded in
`2026-07-16_replay-design.md`.

### What breaks

`offline_lean_replay "<proofDir>"` is the SAW-side discharge path: the
user supplies a Lean proof, and SAW admits the SAW goal iff the Lean
proof kernel-checks against the freshly-emitted obligation. R-1 breaks
that contract on the **completed-outline** path: a user `completed.lean`
that proves `True` (never binding to the real goal) yields CHECK-OK,
and SAW reports the goal proved.

This is not only an adversarial concern — the same class causes
ACCIDENTAL silent misses: any honest `completed.lean` that renders the
goal as `abbrev goal`, `@[reducible] def goal`, a parameter-style
`def goal (x : …) :`, or under a namespace, sets `has_goal_def = 0`
and silently skips the proof↔goal binding check, so a proof that
doesn't actually close the emitted goal can pass without any loud
failure. It is the exact "syntactic proxy under-approximates the
semantic property, read from the wrong file, and a 0 silently disables
the gate" pattern the charter targets.

### Locations (all paths relative to repo root)

- `saw-core-lean/replay/lean-check-core.sh:101-104` — `has_goal_def`
  is computed by grepping the STAGED `Emitted.lean`:
  `grep -qE '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goal[[:space:]]*:'`
- `saw-core-lean/replay/lean-check-core.sh:213-228` — the closer↔goal
  binding gate (both the missing-`goal_closed` check AND the
  `#check (goal_closed : goal)` type check that forces the closer to
  prove the emitted goal) is ENTIRELY inside `if [ "$has_goal_def" -eq 1 ]`.
  When `has_goal_def=0`, NOTHING verifies that any theorem proves the
  goal.
- `saw-central/src/SAWCentral/Builtins.hs:1582` — on the completed
  path, `Emitted.lean` is OVERWRITTEN with the user's `completed.lean`
  (`copyFile userCompleted (stage </> "Emitted.lean")`), so
  `has_goal_def` is derived from attacker/author-controlled content,
  NOT from the authoritative fresh emission.
- `saw-core-lean/replay/lean-check-core.sh:132-146` — the per-def
  drift path (taken when `has_goal_def=0`) was intended for
  module-artifact rows. For the single-`def goal` fresh emission
  wrapped in `namespace GeneratedHarness … end GeneratedHarness`, it
  emits a probe of the form
  `#check (show GeneratedHarness.GeneratedHarness.goal = GeneratedHarness.goal from rfl)`.
  VERIFIED on v4.32.0: the DOUBLED-namespace LHS
  `GeneratedHarness.GeneratedHarness.goal` resolves to a user-supplied
  `def GeneratedHarness.GeneratedHarness.goal`, and `rfl` PASSES. This
  probe is therefore NOT a backstop — it checks def↔def defeq, which
  never forces the goal to be PROVED.

### Reproduction (the confirmed witness)

`proofDir/` with two files:

`completed.lean`:
```lean
import CryptolToLean
def GeneratedHarness.GeneratedHarness.goal : Prop := <verbatim copy of the fresh goal body>
```
`proof.lean`:
```lean
import Emitted
theorem goal_closed : True := trivial
```

Chain of events:
1. `completed.lean` has no bare `def goal :` line ⇒ after Builtins.hs
   overwrites `Emitted.lean` with it, `has_goal_def = 0`.
2. `has_goal_def = 0` ⇒ the step-6 binding gate (lean-check-core.sh:213-228)
   is skipped ⇒ nothing checks a theorem proves the goal.
3. `completed.lean` defines `GeneratedHarness.GeneratedHarness.goal`
   defeq to the fresh goal ⇒ the per-def drift `rfl` probe passes.
4. `proof.lean` proves only `True` ⇒ elaborates cleanly;
   `#print axioms goal_closed` is clean ⇒ axiom audit passes; no
   `sorry` ⇒ placeholder policy passes.
5. ⇒ CHECK-OK ⇒ `offline_lean_replay` returns `SolveSuccess`.

The verbatim goal body is obtained trivially by running `offline_lean`
first (it emits exactly that text). The copy compiles and passes the
source lint (`natPos_macro` etc. are not lint hits). Witness stage
was constructed at
`scratchpad/rev-replay/attack-stage/` during the audit (scratch, not
committed). The obligation used to confirm was
`∀ (x : Bool), x = !(!x)`.

### Both consumers

The identical hole exists in the CI proof harness —
`otherTests/saw-core-lean/support/lean-proof-test.sh:209-212`
(`goal_output_requires_goal_closed` greps the staged completed.lean)
and `:418-425` (skips the `goal_closed : goal` check when
`has_goal_def` is false). The LIVE runtime exposure is the replay
driver (arbitrary user `proofDir`); the CI harness hole matters
because it means the test suite would not catch a regression that
reintroduces R-1.

### Why it survived until now

No negative/boundary test exercises completed-outline goal-binding.
The `saw-boundary/replay_reject_*` rows test axiom introduction and
`sorry`; none test "a completed.lean that does not prove the goal must
be rejected." So the gap had no red row.

### Recommended fix (reviewer's, with detail)

1. **Derive `has_goal_def` from the AUTHORITY, not the user file.**
   The fresh in-process emission (before the Builtins.hs:1582
   overwrite) is the authority. Compute `has_goal_def` from the
   `Generated.lean` / pre-overwrite emission, or pass it in from the
   Haskell driver which knows it emitted exactly one `def goal`.
2. **Require `has_goal_def = 1` on the completed path.** Since
   `offline_lean_replay` ALWAYS emits exactly one `noncomputable def
   goal : Prop`, a completed outline that does not present a bare
   `def goal :` is malformed and must HARD-FAIL — never silently drop
   to the def↔def drift path. Make `has_goal_def == 0` in the
   single-goal replay a `fail`, not a branch.
3. **Harden the drift probe** so `GeneratedHarness.GeneratedHarness.*`
   can never resolve to a user-supplied def — qualify the probe
   against the reference module, or use a fresh gensym namespace not
   derivable by the user.
4. Apply the same three to the CI harness
   (`lean-proof-test.sh:209-212, 418-425`) so replay and CI stay
   identical.

### Regression test to add (would have caught R-1; must fail today)

A NEGATIVE completed-outline row: a `proofDir` whose `completed.lean`
does NOT prove the goal (e.g. the `True`/doubled-namespace witness
above, or an honest-but-mismatched `abbrev goal`), asserted to be
REJECTED by both the replay driver and the CI harness. Pin the exact
rejection diagnostic (per the `.known-gap.expected` / `.expect-fail`
discipline). Place under `saw-boundary/` (SAW-side rejection) and/or a
dedicated `negative`-style replay row. This row must go red on the
current code and green after the fix.

---

## LB-1 (Medium, latent) — raw fix contract decoupled from SAW semantics

**Confidence:** HIGH (two compiled Lean witnesses). **Reachable:**
latent — zero current corpus uses of `saw_fix_choose_raw`.

### What

`saw_fix_unique_exists_raw` / `saw_fix_choose_raw`
(`saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:1230,1235`),
emitted from `lowerFixProofObligation`
(`saw-core-lean/src/SAWCoreLean/Term.hs:3325`, reached at Term.hs:2731).

Unlike the WRAPPED fix contracts (which carry a genuine
productivity/lookback field — see "Cleared" below), the RAW contract's
sole condition is uniqueness among ALL fixed points:
`body x = x ∧ ∀ y, body y = y → y = x`. This is purely EXTENSIONAL —
it cannot observe SAW's operational divergence. So it is provable
while SAW's meaning is ⊥ (the OP-3 hole class, `project_op3_pure_uniqueness_hole`).

### Witnesses (compiled)

- At `Nat` (a DNat raw-position type): the SAW analog of
  `\n -> ite (eq n 0) 7 7` forces its argument (SAW diverges) but is
  extensionally the constant 7 ⇒ the obligation is provable with
  witness `7`.
- At a proof type (DRawProp): `saw_fix_unique_exists_raw P body` is
  VACUOUSLY provable for ANY `body` whenever `P` is inhabited, by
  proof irrelevance; the body is never inspected.

### Reachability

The gate that routes a fix to wrapped-vs-raw is `shouldWrapBinder
typeArg` (`Convention.hs:834`). `DValue`/`DVarValue` (including `Bool`,
the documented OP-3 witness) now route to the guarded realizations or
a loud reject — that specific hole is CLOSED. But `DNat`, `DFunction`,
`DRawProp`, `DRawType`, `DVarRaw` fall through to the raw contract.
So soundness of the raw path rests ENTIRELY on the source recognizer's
routing plus the code's own hedge ("believed corpus-unreachable for
divergent shapes and census-checked", Term.hs comment near :3323) —
NOT on any Lean obligation.

### Recommended fix

Either (a) gate the raw contract behind a lookback-style productivity
obligation analogous to `saw_fix_bounded_productive` (so a divergent
raw fix has no discharge), or (b) have the emitter PROVE (not census)
that no operationally-strict fix reaches the raw path — e.g. restrict
the raw contract to positions where strictness is impossible and
reject otherwise. This is theory-adjacent to the 0.03
fragment-semantics program; coordinate with that.

### Regression / tracking

Add witnesses as negative pins if the contract is tightened. Until
then, keep the `project_op3_pure_uniqueness_hole` memory current with
the precise reachability set above (DNat/DFunction/DRawProp/DRawType/
DVarRaw). Note this is the RAW counterpart of the wrapped fixes that
rev-seams cleared (C1/C2) — the wrapped path is genuinely gated; only
the raw path carries this hole.

---

## V-H1 (Medium, latent) — negative-probe harness accepts any error

**Confidence:** HIGH (witnessed against the real harness).

`otherTests/saw-core-lean/support/lean-negative-test.sh:113` scores a
`*.shouldfail.lean` probe as PASS via
`grep -qE "^[^[:space:]]+: error"` — with ZERO check of WHICH error
fired. A probe that fails for an unrelated reason (a renamed library
symbol, a removed import, an authoring typo) reports green while the
soundness invariant it claims to pin (that `error`/`coerce`/
`unsafeAssert`/`saw_fix_unique_exists` stay shape-constrained) goes
untested. The 5 current probes assert subtle properties (universe
mismatches, `Inhabited` instance-synthesis failure); a refactor that
renames a primitive keeps every probe passing with `unknown
identifier` and never turns red on a genuine loosening.

**Witness:** a probe `example : Nat := this_identifier_does_not_exist_anywhere`
run through the real harness printed
`OK: <probe>.shouldfail.lean rejected as designed`, exit 0.

**Contrast:** differential/obligation known-gap rows REQUIRE
`.known-gap.expected` substrings; the negative harness has no
equivalent.

**Fix:** require each `*.shouldfail.lean` probe to carry an
expected-diagnostic sidecar (like `.known-gap.expected`) whose
substrings must appear in the actual rejection; fail if absent or
unmatched. Add the sidecars for the 5 existing probes as part of the
fix.

---

## V-H2 (Low-Medium, latent) — obligation rows pass on empty emission

**Confidence:** HIGH (witnessed).

`otherTests/saw-core-lean/support/lean-obligation-test.sh:304-345`
(directive loop + `expected.observed` ↔ `test.observed` diff) plus the
compile gate at `:214`: nothing requires at least one
`contains`/`contains-normalized` directive. A row whose `expected.txt`
holds only `absent:` directives passes on a completely EMPTY
`emitted.lean` — every forbidden literal is trivially absent, and an
empty `.lean` compiles clean (`lake env lean` exits 0). Related: an
empty `contains:` literal is also vacuous (`grep -F ""` matches any
non-empty file).

Latent, not active — every current obligation row has ≥1 positive
`contains` — but the harness permits regressing or authoring into a
vacuous row, exactly the class the differential harness already
guards.

**Witnesses:** (a) the harness's exact directive/diff logic
(`:262-338`) run against an empty `emitted.lean` with
`absent:unsafeAssert` / `absent:sorry` → final status 0 (PASS). (b) an
empty `.lean` through `lake env lean` exits 0 with no output.

**Fix:** require ≥1 positive directive (`contains`/`contains-normalized`)
per obligation row; reject empty directive literals.

---

## V-H3 (Low, latent) — dead error-detection regex in obligation observer

**Confidence:** HIGH (witnessed).

`otherTests/saw-core-lean/support/lean-obligation-test.sh:227` uses
`grep -qE '^[^"[:space:]][^:]*: error'`. This does NOT match a real
Lean error line like `…lean-observe.lean:6:17: error(lean.unknownIdentifier): …`
— the `[^:]*` cannot cross the `:line:col:` colons — whereas the
differential/proof/elaborate harnesses use `^[^[:space:]]+: error`,
which DOES match. Currently harmless because the same `if` also tests
`[ "$lean_rc" -ne 0 ]` and Lean exits nonzero on error, so it is a
dead belt-and-suspenders clause; but any future error-but-exit-0
observer diagnostic would slip through.

**Fix:** use `^[^[:space:]]+: error` here too, consistent with the
sibling harnesses.

---

## LB-2 (Low, live) — `missingDocs` is documented as enforced but only warns

**Confidence:** HIGH.

`#guard_msgs` genuinely bites (a wrong expected value → elaboration
error → nonzero `lake build` exit → caught at
`saw-core-lean/replay/lean-check-core.sh:85/89`). BUT `missingDocs`
does NOT: `saw-core-lean/lean/lakefile.toml` sets
`weak.linter.missingDocs = true`, which is a WARNING, and the harness
(and CI) check only the `lake build` exit code — there is no
`warningAsError`, and no warning-grep anywhere. An undocumented public
declaration would `lake build` cleanly (exit 0 + a stderr warning) and
pass every gate. The lakefile comment calls this "enforced," which
overstates the mechanism — the zero-warning state is CONVENTION, not a
gate.

This is a regression against the 2026-07-23 docstrings work (this
audit's own recent history): that commit's message accurately said "a
new undocumented declaration warns in lake build," but the lakefile
comment claims enforcement.

**Fix (if enforcement is intended):** either add
`-DwarningAsError=true` (or the Lake equivalent) for the library
build, or add a harness step that greps the `lake build` stderr for
`missing doc` and fails. Otherwise, downgrade the lakefile comment to
say "surfaced as a warning; zero-warning is convention, not gated."

---

## TIER-1 (Low, live, SAFE direction) — replay is always strict-tier

**Confidence:** HIGH (witnessed).

`offline_lean_replay` invokes the checker with only two script args
(`saw-central/src/SAWCentral/Builtins.hs:1584`:
`readProcessWithExitCode "bash" [coreScript, projRoot, stage] ""`), so
`lean-check-core.sh`'s `$3` (`TRUST_TIER`) is always empty ⇒ strict.
The driver never reads a `.trust-tier` marker from the `proofDir`. The
conformance harness DOES read it (`lean-proof-test.sh:112-120`). So the
two consumers do NOT apply identical per-row tiering — but replay is
STRICTER (never looser): a native-eval (bv_decide) proof discharged via
replay FAILS LOUDLY with `axiom-outside-allowlist`, never admitted.

**Witness:** goal `∀ x y : BitVec 8, x*y=y*x` — no-tier (= replay)
rejects `goal_closed._native.bv_decide.ax_1_5`; native-eval tier gives
CHECK-OK.

This is arguably the correct, safest product posture (native
evaluation is a conformance-suite construct, not a runtime-admission
mechanism). The only defect is that it is undocumented; a reader would
assume both consumers honor the marker.

**Fix:** one sentence in `2026-05-02_residual-trust.md` §3.2b (and/or
proof-cookbook's trust-policy section): "`offline_lean_replay` runs
strict-tier only; the `native-eval` tier is a conformance-suite
construct, never honored at product-runtime admission." No code change
needed for soundness.

**FIXED 2026-07-24:** the tier note now lives in
`2026-05-02_residual-trust.md` §3.2b, alongside the R-1
completed-outline binding note.

---

## SEAMS-D3 (Low, UNCONFIRMED) — type-translation injectivity

**Confidence:** LOW — no witness found; could NOT be proven either way
by static reading.

`EqualitySubjectTypeImage` (`Convention.hs:200`, chosen by
`subjectRepForCarrier` when `asSort aArg`, `Term.hs:2293`) emits `Eq`
over TRANSLATED type-images. IF type translation ever collapses two
SAW-distinct types to one Lean image, an emitted `Eq X_img Y_img`
could be `rfl`-provable where SAW's `Eq X Y` is not — i.e. a
weaker-than-intended obligation. The machinery is defensively built
(all `EqRecConvention` fields derive from one `ρ_eq`, `Term.hs:2329`,
and it is loud on defeq mismatch), and rev-seams found no witness, but
translation-injectivity was not proven.

**Recommended:** a targeted follow-up by whoever owns type-translation
injectivity — enumerate the SAW type constructors that share a Lean
image (e.g. anything mapped to `Type`, Num vs Nat aliases, the
Vec/BitVec pair) and check whether any pair can appear as the two
sides of an emitted type-image `Eq`. Low priority given no witness,
but explicitly OPEN — do not record as cleared.

---

## DOC-1 (Tertiary) — self-test case count drift

`saw-core-lean/doc/proof-cookbook.md:309` says the trust-tier self-test
is "27 cases"; the file (`otherTests/saw-core-lean/support/trust-tier-selftest.sh`)
has 30 (7 end-to-end + 9 pure-awk + 14 pure-lint). One-word fix.

---

## Cleared surfaces (coverage map — do NOT re-audit without cause)

The panel verified these SOUND with reasoning. Recorded so a future
reviewer knows what was covered and can focus effort elsewhere.

### Trust base (rev-leanbase)
- **Exactly two axioms**: `vecToBitVec_bitVecToVec`,
  `bitVecToVec_vecToBitVec` (SAWCorePrimitives.lean:600,604). Every
  other `axiom` grep hit is docstring prose. Nothing else
  axiomatic-in-effect — no `native_decide`, no `sorry`, no
  provability-changing `instance` in the support/proof libraries.
  `#print axioms` on bv theorems = `propext` + these two.
- The two axioms are actually TRUE on the standard model (both
  converters are total MSB-first pack/unpack, `:570,:575`), hence
  mutually inverse and jointly consistent — not merely assumed;
  `decide`-closable at n=0,4,5,6.
- **Endianness** (rev-sawside's routed flag): both converters MSB-first
  (Vec position 0 = MSB), and crucially BOTH share the one convention,
  so the round-trips are identity even on asymmetric values. MSB-vs-SAW
  correctness is a value-fidelity question resolved transitively by the
  fidelity review's `bvToNat = (vecToBitVec v).toNat` unsigned pin (LSB
  would have diverged in the differential matrix).
- WRAPPED fix / stream / mkStream / checked-vector / partial-op
  contracts are each provable-only-when-matching-SAW (details in the
  scratchpad raw findings; key: `saw_fix_bounded_productive.lookback`
  is genuine strict guardedness, and SAWCorePrelude_proofs.lean:830-1029
  DERIVE stabilization/fixed-point/uniqueness from it — no OP-3 hole on
  the wrapped path). `saw_unsafeAssert` closes only via
  rfl/decide/simp-only-[4 proven lemmas]/omega — no fabrication.
  `coerce` = `cast` over a genuine `Eq Type` proof.

### Replay kernel (rev-replay), APART from R-1
- **Placeholder/`sorry` invariant** (rev-seams' D1): a replayed
  artifact with a lingering `sorry` IS rejected — the true enforcer is
  the AXIOM AUDIT (`#print axioms goal_closed` reports `sorryAx`), not
  the source grep, backstopped by step 2 (in-statement sorry
  whitelist, lean-check-core.sh:96-99) and step 4.5 (zero-tolerance on
  proof.lean AND completed.lean, :157-162). No path admits a lingering
  sorry into an admitted goal.
- Axiom allowlist not bypassable: multi-line bracket continuation,
  Cyrillic look-alike `propеxt`, qualified `Foo.propext`,
  wrong-closer-prefix — all rejected; sentinels
  (UNKNOWN-TRUST-TIER/TRUST-TIER-UNUSED) fire into the reject stream.
- Source lint F1 class complete on v4.32.0 (char-literal hiding
  rejected AND independently rejected by Lean; raw/interpolated
  strings, non-ASCII prime, `]'` all fatal; denylist complete vs the
  v4.32.0 escape hatches; LC_ALL=C + nonzero-awk-exit-rejects in both
  consumers).
- Cache-staging fingerprint complete (FNV-1a over names+contents of
  the shipped project files; stale library/toolchain ⇒ different
  fingerprint ⇒ different cache dir; checker script always runs from
  the read-only data dir).
- Fresh-emission-is-authority holds on the NON-completed path
  (`has_goal_def` always 1 there because `writeLeanProp` always emits
  `def goal`).

### Two-tier machinery (rev-tier)
- No input admits a native-eval axiom on a strict-tier row; the
  name-pattern admission (`^goal_(holds|closed)\._native\.bv_decide\.ax_[0-9_]+$`)
  is exact and forgery-proof against the source lint; markers
  non-vacuous; all 30 self-test cases non-vacuous. v4.32.0 emits
  `goal_holds._native.bv_decide.ax_N_M` (not `ofReduceBool`), which the
  pattern matches exactly and no more.

### Emitter seams (rev-seams)
- fix Class-F/Class-S lowerings pass the actual body into an
  obligation that references it (over-acceptance ⇒ unprovable
  obligation, never a wrong value); `adaptTo` chokepoint's only
  meaning-changing adapter is raw→`Pure.pure` (meaning-preserving),
  runtime→raw absent, forbidden adaptations throw;
  `classifyDomain`'s dangerous direction is closed by the PROP-BACKSTOP
  (`Except String P` is ill-typed in Lean 4). All 11 division-family
  partial ops are gated by `PartialOpContracts` (the bare div mappings
  are dead code); the IntMod modulus gate (`evalNatConst`) is exact;
  if0Nat/natCase and raw-position `error` route to wrapped/reject with
  no silent representation change; `mapsToQualifiedTie` Float is
  name-only; ite/iteDep preserve SAW's True-before-False order.

### SAW-side wiring (rev-sawside)
- `offline_lean` never admits on emission (SolveUnknown);
  `verifyObligations` emit-all still fails the run (only ValidProof
  counts); `LeanReplayEvidence` can't be forged/reused (sole producer
  on ExitSuccess; finalization re-checks `sequentSubsumes`; absorbing
  Semigroup); the opaque-set derivation blocks unsound recursors;
  `scLiteralFold` preserves denotation case-by-case; the normalize cap
  fails loud; interpreter registrations are pass-through.

---

## Cross-lane dependency map (for the fixer)

- **R-1 = rev-sawside F-SAW-1 = the failure of rev-seams' D1 binding
  question.** rev-sawside scored it latent ("incidentally protected by
  the broken double-namespaced probe"); rev-replay proved the
  incidental protection is NOT protective (the probe resolves to the
  user def and passes). Treat as ONE finding at CRITICAL.
- **rev-seams' D1** (every emitter obligation is a `sorry` until
  closed) is CONFIRMED enforced by the axiom-audit `sorryAx` catch
  (rev-replay Q1, rev-leanbase). This is INDEPENDENT of R-1 — R-1 is
  about the goal↔closer BINDING, not about `sorry`. Both must hold; the
  `sorry` half does, the binding half (completed path) does not.
- **rev-seams' D2** (un-gated total primitives: intToNat, sbvToInt,
  intToBv, intAbs/Min/Max, signed bvSDiv/bvSRem overflow) is the
  ground the `2026-07-23_fidelity-review.md` already swept — cross-check
  its per-definition verdicts against rev-seams' D2 list before
  treating as closed (fidelity review found no divergence in these
  beyond the already-fixed bvToInt).

## Files of record

Reviewers' raw findings (full text, all six lanes):
`scratchpad/2026-07-24_audit-findings-raw.md` (session scratch — not
committed; the salient content is reproduced above).

Key source locations: `saw-core-lean/replay/{lean-check-core.sh,
axiom-audit.awk, proof-source-lint.awk}`; `otherTests/saw-core-lean/support/{lean-proof-test.sh,
lean-negative-test.sh, lean-obligation-test.sh, trust-tier-selftest.sh}`;
`saw-central/src/SAWCentral/Builtins.hs:1441-1614`;
`saw-core-lean/src/SAWCoreLean/{Term.hs, Convention.hs, Contracts.hs,
FixRecognizer.hs, SpecialTreatment.hs}`;
`saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean`.

## Recommended sequencing (not yet executed — held for review)

1. **R-1** (CRITICAL, must-fix-before-release): the four-part fix
   above + the negative completed-outline regression row, applied to
   BOTH consumers. Gate: the new row goes red before, green after;
   full suite green. — **DONE 2026-07-24** (see the FIXED note in the
   R-1 section).
2. **V-H1** (Medium): expected-diagnostic sidecars for negative
   probes + the harness requirement.
3. **LB-1** (Medium, latent): coordinate the raw-fix contract gating
   with the 0.03 fragment-semantics program; until then keep the
   reachability record current.
4. **V-H2 / V-H3 / LB-2 / TIER-1 / DOC-1**: housekeeping guard/doc
   fixes, batchable.
5. **SEAMS-D3**: targeted type-translation-injectivity follow-up
   (open; low priority; do not mark cleared).
