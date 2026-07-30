# Release gate — WAVE 3 audit and remediation plan (2026-07-30)

Five docket lanes (the items wave 2 logged rather than settled) plus
five fresh Opus lanes, every finding adversarially refuted
(refute-by-default), surviving CRITICAL/HIGH given a second
independent lens, every docket verdict given a skeptic, and the wave
itself critiqued for completeness. 87 agents, HEAD `fd1201f9d`.

24 findings survived refutation; 19 were refuted. **2 CRITICAL, 6
HIGH** (one HIGH reinstated by the critic).

**DO NOT RELEASE.**

## 1. The scorecard: the convergence proposal's §5 prediction is REFUTED

§5 predicted: *"wave 3's CRITICALs will be in the six enumerations
above, and nowhere else… If wave 3 instead finds a CRITICAL in a
derived enumeration or in a by-construction chokepoint, the diagnosis
is wrong."*

That trigger fired, on three independent counts:

| # | Fact | Why it refutes |
|---|---|---|
| 1 | **K-2 is a CRITICAL in a chokepoint** — the digest guard is deletion-blind and the completed-path selector is unlatched filesystem state | §5's stated trigger condition, met literally |
| 2 | **W2-UNRUN-1 (reinstated CRITICAL) is a chokepoint** — the telescope pin does not cover the shape it was believed to cover | a second CRITICAL outside the six |
| 3 | **Even the confirming CRITICAL (K-1) is outside the six** — its home, `proof-source-lint.awk`'s ban list, is not in §4's table | "in the six and nowhere else" is false in *both* directions |

What survives is the *mechanism* half: hand-maintained lists do rot,
and they dominate this wave by volume (13 of 14 gate-path
divergences, F-W3-HE-3/4/5/6, W3-REF-5, W3-HR-5/8/9, K-8). But the
proposal's frame — that enumeration discipline is the *single cause*
— does not reach where this wave's CRITICALs actually live: **the
trust kernel's ordering and existence assumptions** (K-1, K-2, K-3,
CP-1, CP-2). That is the corrected diagnosis, and §5 must be rewritten
to say so rather than quietly restated.

§6's own hedge also landed. I claimed the type-collapse class had
"exactly five members." It does not: **`bitvector`**
(`SpecialTreatment.hs:685` → `SAWCoreBitvectors.lean:32`) is a
genuine unswept same-shape member. §6 named this exact risk — "I
cannot enumerate reliably even when I am specifically trying to" —
and it was right.

## 2. BLOCKS RELEASE

### K-1 (CRITICAL, hand-enum) — the proof-side lint's ban list misses `simproc`

`replay/proof-source-lint.awk:208-211` bans
`axiom|macro|macro_rules|elab|elab_rules|run_cmd|…|export`. **Verified
independently: `simproc` appears nowhere in the file (0 occurrences).**
The `simproc` / `dsimproc` / `builtin_simproc` family is present in the
pinned v4.32.0 toolchain and gives a proof-side file
elaboration-time IO plus unchecked `addDecl`. Separately, the
alternation's word-boundary class includes `_`, so every
`*_elab`-suffixed command (`declare_config_elab`) also escapes.

A machine-checked payload was constructed by the audit (scratch only,
never executed): a `simproc` that adds a forged `thmDecl` to the
environment and performs file IO during `simp`.

**Fix (by construction, not another list entry):** invert the lint
from a denylist of banned command heads to an **allowlist of
permitted** top-level command heads. Top-level heads in a proof-side
file are a small closed set (`import`, `open`, `section`, `namespace`,
`end`, `variable`, `theorem`, `lemma`, `example`, comments); tactic
vocabulary lives inside bodies and is unaffected. Then an unknown
future Lean command fails **closed** instead of open, which is the
only version of this fix that does not rot at the next toolchain
bump. Measure the cost against every `proof.lean` in the tree first,
as that file's existing discipline requires.

### K-2 (CRITICAL, chokepoint) — deletion-blind digest guard + unlatched path selection

Two verified defects that compose:

1. `verify_unchanged` (`lean-check-core.sh:130-139`) opens with
   `[ -f "$STAGE/$f" ] || return 0` — **it returns SUCCESS for a file
   that no longer exists.** The guard quantifies over mutation only.
2. The completed-vs-plain path is re-derived from mutable filesystem
   state at eight `[ -f … ]` sites (`:172, :253, :254, :298, …`)
   rather than latched at staging.

Deleting `$WORK/completed.lean` mid-check therefore silently converts
the completed path into the plain path, dropping the drift check —
**the only thing binding the user's `def goal` to the SAW
obligation** — while both guards report success.

**Fix:** (a) `verify_unchanged` must distinguish "never staged" from
"staged, then deleted": a file with an entry in `STAGED_DIGESTS` that
is now absent fails `user-file-deleted-mid-check`. (b) Latch the path
decision once at staging into a single variable and branch on that
everywhere; no gate may re-ask the filesystem what kind of check this
is.

### W2-UNRUN-1 (CRITICAL, chokepoint) — REPRODUCED; reinstate, do not retract

Wave 2's finding that I could not reproduce **is real**, and my
failure to reproduce it was a single-test-case artifact. From an
ordinary Cryptol module (`v = [7, error "e"]; h = (v @ 0) < 100`)
plus `goal_cut`, `offline_lean` emits a goal whose Pi spine is

```
@Eq.{1} (Except String Bool) (… saw_throw_error …) (Pure.pure Bool.true)
  -> @Eq.{1} Bool Bool.false Bool.true
```

— an Except-carried, uninhabited binder domain with a carrier-free
false consequent, **while SAW independently proves the same
hypothesis true**. No `parse_core`, no free type variables. Four
hypothesis-bearing goals were emitted in the lane, including a
deliberately error-free control.

Why I got it wrong: the telescope pin's ARITY half fires only when the
**antecedent** contains a repeated subterm, which hoists the P-1 `let`
above the Pi so `leanPiSpineArity` scores 0 (`Signature.hs:251-253`).
A repeat in the **consequent** leaves the arrow intact and the goal
emits. The binder-TYPE half is structurally blind (both sides
`FpOther`), as `TODO.md:357-362` already logged.

Aggravating, and its own finding: **`saw-boundary/goal_hypothesis_refusal`
is green for a reason other than the one it claims** — its
`.log.good` records "SAWCore goal binders: 1; emitted Lean goal
binders: 0", i.e. it was refused by the let-hoist arity accident, not
by the shape. That is a V-H1 (a probe passing vacuously) sitting on
top of a real hole, and `Exporter.hs:1436-1461` asserts a measured
gate that the error-free control falsifies.

**Fix:** land the refuse-on-`Except`-carried-binder-domain gate, scoped
to `writeLeanProp` (**not** shared code — `obligations/proof_bv_eq_to_eq/expected.txt:7`
is a landed row with that shape arriving via `write_lean_term`);
correct the false comment; re-cut the boundary row so it refuses for
the stated reason. Corpus cost is zero.

### CP-1 (HIGH, chokepoint) — digest not re-verified before post-elaboration consumers

Last `verify_unchanged proof.lean` is `:351`; `cp "$STAGE/proof.lean"
"$STAGE/UserProof.lean"` is `:418`, with a second copy at `:452`.
The audited artifact and the closer list are built from bytes no text
gate ever saw. **Fix:** re-verify immediately before each consumer, or
better, copy from a latched staging snapshot rather than from
`$STAGE`.

### CP-2 (HIGH) — same root as K-2; fix together.

### K-3 (HIGH, hand-enum) — REINSTATED by the completeness critic

K-3 was refuted on the ground that "no elaboration-time IO route
survives GATE B." **K-1 is exactly that route**, and the same wave
confirmed it. The wave held both positions at once; the critic caught
it. Reinstate at HIGH (CRITICAL in composition with K-1). K-7's
scenario 2 likewise returns at MEDIUM.

## 3. Should fix before release

- **W3-REF-1 (HIGH, derived-enum)** — the spelling lint I landed
  yesterday is *spelling-bound*: its extractor matches the literal
  token `Lean.Ident "`, and nine bare library citations the emitter
  writes today escape both it and `emitterBareNames`. The derived
  check is real but its derivation source is the wrong one.
- **W3-HR-4 / W3-REF-3 (HIGH/MEDIUM, derived-enum)** —
  `supportLibraryFiles` uses `listDirectory` (**verified
  non-recursive**), and the agreement test reads only the root
  module's imports, so a support module in a subdirectory is invisible
  to both. Latent today (no subdirectories exist) — which is precisely
  how the previous five rotted.
- **`bitvector` unswept type-collapse member** — see §1.
- **Anti-trivialization gate is fail-OPEN (CP-3 + K-5)** — any
  non-zero probe exit (timeout, failed write) reads as "not trivial."
- **Gate-path divergences (13 confirmed)** — highest value: the cabal
  path *replaces* rather than extends the environment;
  `SAW_LEAN_FAIL_ON_KNOWN_GAPS` is dropped on one path; the two paths
  can test **different saw binaries**; the strictest verb is unwired.
  One mechanism should own env construction for all three paths (there
  is a third: CI).
- **LIB-W2-2 residue (MEDIUM-HIGH)** — `Obligations.hs:535-541`'s
  guarantee is still false; three latent unswept members.

## 4. Coverage debt and doc corrections

- **OBL-1 is MEDIUM, not HIGH, and OBL-2 DOES NOT EXIST.** The lane
  authored a HIGH, called it "confirmed and stronger than filed," and
  its skeptic found no OBL-2 anywhere: `grep OBL-2` returns one hit
  whose body is OBL-1's content. Correct the ledger; do not carry a
  phantom finding forward. Real content: five byte-identical
  `expected.txt` (md5 `a494642d…`), and only three of six directives
  are live.
- **README LIB-1 wording** — MEDIUM *incompleteness*, not the falsity
  wave 2 claimed (one of the two quoted sentences is true). The
  stronger sibling is the now-false in-source comment at
  `Exporter.hs:1436-1446`.
- MEDIUM/LOW hand-enum items: F-W3-HE-3 (three `skip` rows name
  non-existent Lean realisations), F-W3-HE-4 (two divergent
  keyword lists), F-W3-HE-5/6 (waiver reasons naming the wrong
  mechanism — including two of the nine *I* wrote yesterday),
  W3-REF-4/5, CP-4/5/6, W3-HR-5/8/9, K-8.

## 5. Method notes, for the next wave

- **The wave contradicted itself and only the critic caught it** (K-3
  vs K-1). A cross-finding consistency check belongs in the harness,
  not in a single critic at the end.
- **12 of 25 docket verdicts were skeptic-flagged** — overclaiming is
  the dominant lane failure mode, including inventing a finding ID
  (OBL-2) and census figures off by ~40%. The skeptic layer paid for
  itself; keep it.
- **One surface no lane read:** `FixRecognizer.hs` (461 lines) — a
  hand-written syntactic classifier whose own comment says a
  misclassification "would be unsound to lower," consumed at
  `Term.hs:1303-1312`. That is a CRITICAL-class admissibility gate,
  implemented as a hand enumeration, never opened. **Wave 4's first
  charge.** Also unread: the shipped `examples/saw-lean/` demo as a
  replay consumer, and `saw.cabal:41-49`'s hand list of shipped
  kernel files (non-recursive glob).
- The audit lens that constructed the K-1 payload wrote a
  theorem-forging `simproc` to scratch. It was never executed and
  never entered the repo (verified: no `pwned.txt`, no build
  artifacts, tree clean at `fd1201f9d`). Red-teaming our own proof
  checker is the point of that lane, but the probe should live in the
  test suite as a pinned negative row once K-1 is fixed — which is
  also the mutation that proves the fix.
