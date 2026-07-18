# SWE / Naming Quality Review (upstream-reviewer pass)

2026-07-17. Independent fresh-context review of the saw-core-lean
backend as an upstream maintainer would see it at merge time.
Scope: naming, module structure, dead code, docs, API surface —
explicitly NOT soundness (tracked separately as the pre-release
soundness audit in TODO.md). Reviewed against the `saw-core-rocq`
parity baseline.

## Naming verdict: KEEP `CryptolToLean`, document provenance

The name is exact parity with Rocq's own `CryptolToRocq`
(`saw-core-rocq/rocq/handwritten/CryptolToRocq/`; `_RocqProject`
binds `-Q … CryptolToRocq`). The "misdescribes the backend"
objection is literally true of *both* backends, but a Lean-only
rename would manufacture a divergence to fix a cosmetic one and
split the two backends' mental model. It is also defensible on its
own terms — the support tree genuinely contains
`CryptolPrimitivesForSAWCore`.

- **Decision (user-ratified direction 2026-07-17):**
  keep-with-documentation. Provenance note added to
  `saw-core-lean/README.md` (Layout section). If the name must ever
  change, do it as a *coordinated* `CryptolTo{Rocq,Lean}` rename
  upstream, not Lean-only.
- Why rename is a bad trade even setting parity aside:
  `CryptolToLean` appears in ~1,925 files under
  `otherTests/saw-core-lean/` (~166 `*.good` goldens plus emitted
  `.lean`/log fixtures), 36 occurrences across 5 Haskell source
  files, the lakefile package name + 80 support-library files, the
  trust kernel's hardcoded axiom allowlist
  (`lean-check-core.sh`), and the external `saw-lean-example`
  consumer (committed `Emitted.lean`/`proof.lean`/`.olean`).
  Re-pins essentially every golden for ~zero user benefit, and
  destroys baseline history right before the pre-release soundness
  audit.

## Primary findings, ranked

### 1. Trust kernel lives under the test tree and is on the product runtime path — should-fix, arguably blocker

`otherTests/saw-core-lean/support/lean-check-core.sh` is the
factored trust kernel. The product builtin `offline_lean_replay`
locates it at runtime as
`SAW_LEAN_ROOT </> "otherTests" </> "saw-core-lean" </> "support"
</> "lean-check-core.sh"` (`saw-central/src/SAWCentral/Builtins.hs`
~1469) and runs it via `readProcessWithExitCode "bash"`. The code
already concedes "Packaging a relocatable installation is release
work." A file that gates whether a proof obligation is *admitted*
should not live in a directory named "tests," reachable only via an
env var into a source checkout — it cannot ship in an installed
binary, and it reads as deletable scaffolding.

**Fix:** move it under `saw-core-lean/` proper (e.g.
`saw-core-lean/replay/`), update the harness reference and the
`Builtins.hs` path, and resolve via a Cabal `data-files` dir rather
than `SAW_LEAN_ROOT`. Blast radius: that path string + harness
delegators + `2026-07-16_replay-design.md`. No goldens.

### 2. `Term.hs` is 6,776 lines (Rocq's is 707) — should-fix

Claims to "Mirror `SAWCoreRocq.Term` in scope and structure" but is
~10× its size; `SpecialTreatment.hs` is 1,039 vs 586. Much excess
is *earned* scope Rocq lacks (obligation emission, position/callee
calculus, proof-carrying lowering), but it shouldn't all live in
one module. Split points already exist as banner sections: the
convention calculus, recursor lowering, and
proof-carrying/partial-primitive/obligation lowering. Extract at
minimum `SAWCoreLean/Obligations.hs` and
`SAWCoreLean/Convention.hs`. The single biggest readability
objection a maintainer would raise at merge.

### 3. README "Tests" section + `lean-shape-test.sh` describe the removed `shape/` category — should-fix, cheap

`README.md` described `{shape,saw-boundary,proofs}` with "Soundness
shape probes (`shape/`)"; `shape/` was removed 2026-07-15 and the
tree is now 11 categories. [README FIXED 2026-07-17 — rewritten
against `test.sh`'s taxonomy header, which is current.] Remaining:
`support/lean-shape-test.sh` is named for the removed category (it
now serves `negative/`) and still resolves
`.../{shape,saw-boundary}/<name>/` internally — rename the script
and drop the dead path.

### 4. `TODO.md` (2,200 lines) is three documents in one — should-fix

81 completed/superseded markers vs 28 open; a 486-line
`## Operative Priority (COMPLETE 2026-07-11)` block inline; plus
`## Audit History` and `## Decision Log`. Split: keep open items in
`TODO.md`; move Audit History + Decision Log to durable `doc/`
files; relocate the large COMPLETE blocks to `doc/archive/`.

### 5. `doc/` mixes 39 dated working-notes with 4 durable refs at top level — should-fix

43 top-level `.md`: 4 durable (`architecture`, `contributing`,
`getting-started`, `proof-cookbook`) + 39 dated notes, several
superseded, alongside a 40-file `doc/archive/`. Contradicts the
README's "Top-level docs are the current as-of-today reference."
Sweep dated/superseded notes into `archive/`, keeping durable docs
plus the few dated ones the README canonizes
(soundness-boundaries, residual-trust, release-plan) at top level.

### 6. Test-category names overlap on "proof" — should-fix

Three siblings use "proof(s)" with three meanings: `proofs/`
(end-to-end discharges), `proof-gaps/` (known-incomplete),
`support-proofs/` (support-library conformance lemmas, all named
`conformance_*`). Rename `support-proofs/` → `conformance/` and
document the `proofs` vs `proof-gaps` split in `test.sh`'s header.
Blast radius: harness `case` arms + Makefile targets; `git mv`
moves no goldens.

## API surface (saw-central) — solid, nits only

- `writeLeanProp` sits with `writeLeanTerm`/`writeLeanCryptolModule`
  — correct placement, consistent `writeLean*` naming, parity with
  the Rocq exporters.
- `LeanReplayInfo`/`LeanReplayEvidence` and `leanReplayFingerprint`
  are cleanly named and Lean-scoped; `LeanReplayEvidence` correctly
  enters the `Evidence` sum type as a first-class audited producer.
- Builtin names are clean parity: `write_lean_*`/`offline_lean`
  mirror `write_rocq_*`/`offline_rocq`; `offline_lean_replay` has
  no Rocq analog — correctly, since kernel replay is the Lean
  backend's reason to exist.
- Nit (nice-to-have): `leanReplayGoalHash`/`leanReplayProofHash`
  are an FNV-1a provenance label explicitly "not verification
  material"; a haddock note that these are not integrity hashes
  would pre-empt a reviewer question.

## Dead code / debris — largely clean

- Zero TODO/FIXME/XXX/HACK in `saw-core-lean/src/`.
- The obsolete lowerings the README calls removed (`mkStreamFix`,
  `mkStreamFixPair`, `genFix`) have no residual references in
  `src/` or `lean/` — removal was complete.
- `Term.hs` export list deliberately trimmed to consumed names.
- `lean/demoProbe/` and `otherTests/saw-core-lean/.snapshots/` are
  gitignored and untracked — local scratch, not committed debris.
- Minor: the `saw.cabal` `library saw-core-lean` stanza pointed
  newcomers at a design doc now in `doc/archive/`. [FIXED
  2026-07-17 — repointed to `doc/architecture.md`.]

## Parity scorecard

| Dimension | Rocq | Lean | Verdict |
|---|---|---|---|
| Haskell module root | `SAWCoreRocq` + `Language.Rocq` | `SAWCoreLean` + `Language.Lean` | Faithful mirror |
| Cabal packaging | `library saw-core-rocq` in umbrella `saw.cabal` | `library saw-core-lean`, same file | Faithful mirror |
| Support-lib namespace | `CryptolToRocq` | `CryptolToLean` | Faithful mirror — keep |
| Builtin names | `write_rocq_*`, `offline_rocq` | `write_lean_*`, `offline_lean`, +`offline_lean_replay` | Faithful + justified extension |
| `Term.hs` size | 707 lines | 6,776 lines | Divergent — earned by scope, but split (#2) |
| Trust-kernel placement | n/a | under `otherTests/`, on runtime path | Lean-specific problem (#1) |

**Merge-gate summary:** the two items an upstream maintainer would
insist on before merge are #1 (trust kernel out of the test tree)
and #2 (split `Term.hs`). #3–#6 are should-fix doc/naming hygiene;
the naming question resolves to keep-with-documentation.
