# Handoff: environment and in-flight state (2026-07-26)

Written for a compute-platform switch. **Technical state is NOT
here** — it is in `TODO.md` (§"Where this stands") and in
`doc/2026-07-26_lib1-carrier-scoping.md`. This file covers only what
a fresh environment will not reproduce on its own.

## Repository state

- Branch `saw-core-lean`, HEAD `e0ae5a185`, **pushed** to
  `origin/saw-core-lean` (`git@github.com:septract/saw-script.git`).
  Working tree clean. Nothing is stranded locally.
- The 2026-07-25/26 audit-remediation work is commits `75c2acfc6`
  through `e0ae5a185` (10 commits).

## Build invocations that actually work

The sandbox needs these exact shapes; deviating triggers permission
prompts or opaque failures.

```sh
# Haskell. CABAL_DIR is required — the default ~/.cabal/logs is not writable.
CABAL_DIR="$TMPDIR/cabalhome" cabal build exe:saw

# Lean support library.
cd saw-core-lean/lean && lake build

# Full suite (~45-90 min; SAW must be found explicitly).
cd otherTests/saw-core-lean
SAW=$(find <repo>/dist-newstyle -name saw -type f -perm -111 | head -1) \
SAW_LEAN_ROOT=<repo> bash test.sh test
```

Known-benign noise: `otool`/`ar`/`install_name_tool` print
`couldn't create cache file … xcrun_db-…` under the sandbox. These
are **cosmetic** — `xcrun` uses the system temp dir, not `TMPDIR`,
and the build still succeeds with exit 0. Do not disable the sandbox
over them.

## Suite discipline (learned the hard way this session)

- **Never edit source, test data, or the Lean library while the suite
  is running.** The harness reads them mid-run and the measurement
  becomes meaningless.
- **Do not run `bash test.sh good` wholesale** to fix golden churn.
  It regenerates every driver and workflow golden and will mask a
  real regression behind cosmetic ones. Regenerate the affected rows
  individually, after reading each diff.
- When a run has one failure and the fix touches only that row's own
  files, report the result as "full run + targeted rerun", not as a
  clean run. Several results this session are of that shape.

## Flakes to expect

- `proofs/llvm_doubleround_comp` intermittently reports
  **"emitted .lean did not compile — emission drift"** under
  full-suite load, with only linter warnings and no error in the log,
  and passes standalone. Almost certainly resource exhaustion — this
  row family is heavyweight (a backgrounded Salsa20 run once consumed
  ~100 GB). Filed in `TODO.md`; the verdict's ambiguity is the actual
  defect, since it is indistinguishable at a glance from a genuine
  drift.

## Nothing else is stranded

Two artifacts lived only in the session scratchpad and have been
moved into the repository:

- the option (c) prototype → appendix of
  `doc/2026-07-26_lib1-carrier-scoping.md` (both theorems, verbatim,
  with their axiom sets);
- the `Vec n Bool` witness that refuted the type-directed carrier
  split → inline in the same doc.

Suite logs and the scratch `.saw` probes were transient measurement
output and are not worth carrying; every conclusion drawn from them
is recorded with its numbers in `TODO.md` or the scoping doc.

## Calibration note for whoever picks this up

Three changes this session were locally well-reasoned and wrong in a
way only the full suite could show: an F-8 gate that false-positived
on legitimate rows, a naming fix that churned 77 rows by conflating
the emitter's generated binders with the names it references, and the
belief that LIB-1 option (a) was viable — refuted by one witness.

The pattern is that reasoning about *this* translator's emitted
output is unreliable without measurement, because the interesting
cases are ones where the emitted shape differs from the mental model
of it. Budget for the full-suite gate on every batch; treat a grep
over `.lean.good` files as a hypothesis, not a result.
