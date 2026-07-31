# Convergence close-out plan (0.02 release arc)

Branch: `saw-core-lean-0.02-closeout` (from `saw-core-lean` at
`e5a0d59b4`). Written 2026-07-30, at the end of the wave-4 fix arc,
BEFORE any of the work below runs — in particular the §5 exit
criterion is fixed now so it cannot be retrofitted to whatever wave
5 happens to find.

Context: `doc/2026-07-30_release-gate-audit-wave4.md` (wave-4
verdict and the W5-1..3 charges), `TODO.md` § "Release gate — WAVE
4 findings" (dispositions as of `e5a0d59b4`: W5-1 closed, W5-2
remedied-not-determined, W5-3 partial), and `residual-trust.md`
§ Threat model (the severity rule everything below is scored
against).

The convergence claim this arc tests: the remaining findings are
small, in-model, fail-closed, and cheaper to fix than to
re-litigate. Each step below either converts an argued claim into
an observed one, retires a hazard class outright, or (wave 5)
adjudicates the claim.

## Step 1 — observation gaps: make argued claims observed

All small and stable per the threat model's own fix rule.

- **SHIP-2 row**: a suite row that exercises the data-files/cache
  branch of `resolveLeanReplayAssets` (`saw_datadir` +
  `XDG_CACHE_HOME`, `env -u SAW_LEAN_ROOT`, synthetic datadir built
  from the `saw.cabal` data-files stanza). This is the only code
  branch no suite reaches; the row simultaneously pins the SHIP-4
  race fix, the `lean2-` schema bump, and the fingerprint/staging
  logic — all currently argued structurally, observed only in
  one-off verifier runs.
- **SHIP-3 check**: the `ship-list.sh` closed check (sketch in the
  wave-4 finding): data-files stanza ≡ tracked runtime assets; no
  subdirectories under `CryptolToLean/` (the non-recursive-glob
  precondition); `relFiles` names present in `Builtins.hs`.
- **Toolchain pin convergence**: demo `proof/lean-toolchain`
  4.29.1 → 4.32.0 (the support library's pin). ELIMINATES the
  shared-tree clobber class rather than warning about it; retires
  the README warning, the getting-started caution, and the TODO
  item. Gated on the demo discharges still closing under 4.32.0 —
  the one risky `lake build`, run serialized with nothing else.
- **FXC-6**: qualify the `"Stream"` datatype ident test in
  `FixRecognizer.hs` (module-qualified like the file's other 14
  ident tests).

## Step 2 — re-score the wave-3 "SHOULD FIX BEFORE RELEASE" list

The last pre-threat-model debt in the ledger (`TODO.md`, wave-3
section): W3-REF-1 (spelling-bound citation lint), W3-HR-4/W3-REF-3
(non-recursive `supportLibraryFiles` walk), CP-3+K-5
(anti-trivialization gate fail-OPEN), the 13 gate-path env
divergences, LIB-W2-2 (Obligations.hs guarantee). Score each under
the threat model with a written disposition. Expected survivors as
real in-model items: the fail-open anti-trivialization gate (the
one place tool failure currently fails open, against rule C3) and
the gate-path env divergence (one mechanism should own env
construction; this class already cost a full suite run). Fix
whatever survives at MEDIUM+; document the rest. Each fix gets the
standing opus fix-audit.

## Step 3 — CI round-trip (user action; parallel with 1–2)

Push/trigger CI once. The fixed demo step answers the W5-2
determination (was the `saw-core-lean-tests` leg red or not
running since 2026-07-18?) and validates `bundle_files` against a
real bindist. Record the answer in `TODO.md` W5-2. Nothing else in
this plan depends on it, but wave 5 should cite it, and §5's
criterion requires the leg observed green once.

## Step 4 — wave 5, the verdict wave

Small panel (~8–10 agents) against the settled tree, only after
steps 1–2 land:

- CONFORMANCE.md:60 semantic re-read lane (does each row pin what
  the table says it pins — the W5-3 remainder).
- Delta-composition lane over THIS arc's commits (the 2026-07-30
  fix arc landed ten commits under per-fix audits; nothing has
  cross-read their composition — the exact gap wave 4's delta lane
  existed for).
- Adversarial verify on MEDIUM+; the cross-finding consistency
  agent; a completeness critic.
- Deliberately NOT pre-fixed, so wave 5 confirms or demotes them
  first: FXC-4/5/7/8, FXS-1/2, DEMO-7/8, the FXC-2
  `isIdentityStreamRead` unit pin (needs `Stream#rec` construction
  machinery in SmokeTest — build it only if wave 5 says the pin
  earns its cost; the H_prod refutation row already carries the
  discrimination side).

## Step 5 — exit criterion and declaration (fixed NOW)

The release gate is met and 0.02 cuts from the release commit iff
ALL of:

1. Wave 5 reports nothing above LOW (after verification, scored
   under the threat model).
2. Every in-model MEDIUM+ anywhere in the ledger is fixed-and-pinned
   or carries an explicit user-accepted disposition.
3. At the release commit: full cabal-path suite green, smoketest
   green, both kernel selftests ALL CASES OK, doc-claim-lint green.
4. The CI `saw-core-lean-tests` leg (including the demo step) has
   been observed green at least once (step 3).

Remaining LOWs ride the ledger into 0.03 alongside the scheduled
LIB-1 program (do NOT start 0.03 early — standing user decision).

Failure clause: if wave 5 surfaces a MEDIUM-or-worse in a
previously-audited surface, the convergence diagnosis (two
populations: translator cured by derivation, kernel cured by scope
reduction) takes real damage — reassess the diagnosis in a doc
before fixing the finding, per the §5-prediction discipline the
convergence proposal established.

## STATUS (2026-07-30, end of the first close-out session)

**Steps 1 and 2 are COMPLETE and gate-swept green** (full
cabal-path suite PASS at `e2d6b3871`, 1392s; smoketest 94/94; both
kernel selftests ALL CASES OK; doc-claim-lint green; six commits
`98e908559..e2d6b3871`, each fix under an opus audit, every audit
finding fixed or dispositioned same-session). Highlights beyond the
step definitions: the triviality gate was hardened through THREE
audit rounds (fail-open → line-position check → refutation-shape
allowlist → allowlist + give-up denylist over the transcript, with
the launder channel proven from Lean's own source and the denylist
mutation-verified); the audit chain also caught the recursive-glob
semantics gap in both new checks, the cold-leg observation gap, and
two ledger-lag instances. Recorded residuals: the launder
denylist's future-phrasing sliver (pinned-toolchain argument, in
the kernel comment); `:(glob)` red-direction unpinned; the
trivgoal_deep harm-story assertion; elan-download time inside the
120s cap (network-bound, not a CI exposure).

**Step 3 (user)**: pending — one CI run answers the W5-2
determination and exercises the fixed demo step + bindist assets.

**Step 4 (wave 5): RAN 2026-07-30 evening**
(`doc/2026-07-30_release-gate-audit-wave5.md`). Verdict against §5:
gate NOT met at `237310fda` — clauses 1+2 failed on bookkeeping
(the S-2/LIB-2 documentation-propagation class, one CONFIRMED
MEDIUM; six ledger MEDIUM+ items without accepted dispositions),
zero CRITICALs, zero translator/kernel defects, failure clause did
NOT fire. Remediation steps 1-2 applied same evening
(`d8e0f8612`): propagation fixed across five files + shipped
docstrings; ledger pass done; clause 3 re-established at
`d8e0f8612` (full sweep PASS 1436s, smoketest 94/94, doc-lint +
ship-list + selftests green).

**§5 state at `d8e0f8612`**: clause 1 — wave 5 reported one MEDIUM
(now fixed; the calibration note that it was the outlier vs the
same-class LOW is recorded, unadjudicated); clause 2 — PENDING USER
ACCEPTANCE of the six proposed dispositions (TODO.md WAVE 5
section); clause 3 — MET at `d8e0f8612`; clause 4 — pending
merge/CI (user decision). The declaration itself is therefore a
user call: accept the dispositions (with or without the OBL-1 pin),
settle clause 1's strict-vs-remediated reading, merge, observe CI.

**§5 state update, 2026-07-31 (user fast-path decision — "I agree
with your recommendations, go ahead with the fast path"):**
- Clause 1 — USER-ACCEPTED reading (i): satisfied-by-remediation.
  Wave 5's one MEDIUM was fixed, swept, and audited the same
  evening it was reported; the consistency agent's calibration
  note (the MEDIUM was the outlier against the same-class LOW)
  stands on record; the failure clause never fired. Recorded here
  so the reading is a decision, not a drift.
- Clause 2 — dispositions accepted and executed: OBL-1
  fixed-and-pinned (differentiated goldens, cross-matrix
  verified); F8b closed as unconstructible (F-9 treatment); F11,
  LIB-W2-3, F12-successor accepted as explicit 0.03 carries;
  W2-UNRUN-2 threat-model re-score commissioned (result at its
  ledger entry). Clause 2 is MET when that re-score's disposition
  lands.
- Clause 3 — to be re-established by a fresh full sweep at the
  release commit (this update and the fixes move it).
- Clause 4 — merge first, then the REMOTE CI run (user-confirmed:
  the GitHub Actions run, not a local one — nothing local can
  satisfy the clause, answer the W5-2 history question, or
  exercise the runner-built bindist).

## Standing constraints for the arc

Per-fix opus audits; no `cabal build` while a suite runs; kernel
(`replay/`) and selftest files never edited while a suite runs;
suite output captured to files, never piped through `tail`;
commits local to this branch, never pushed; `test.sh good`
regenerates ALL goldens — don't.
