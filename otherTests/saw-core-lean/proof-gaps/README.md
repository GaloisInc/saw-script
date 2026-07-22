# Proof Gaps

This directory keeps proof attempts and explicit proof-gap notes that are
useful stress cases but are not accepted backend proof regressions yet.

The default `proofs/` sweep is for obligations that elaborate and pass the axiom
audit under the trust policy (two tiers since 2026-07-21 — see
`saw-core-lean/doc/proof-cookbook.md`, "Bitvector automation trust policy":
strict by default; a row may opt into the loudly-labeled `native-eval` tier via
a `.trust-tier` file, which admits bv_decide's per-invocation native axioms for
that row only, with the lean-smt migration recorded as the resolution). BV-heavy
proofs still land HERE when they time out under the per-process budget or need
automation that neither tier sanctions. Keeping them out of `proofs/` prevents
the default regression suite from treating unavailable automation as a green
proof-discharge path.

Small proof examples can also live here when the backend now emits a sound
proof-carrying obligation but the proof-support phase has not yet discharged
that obligation. For example, E4/E5 now expose checked vector bounds contracts
inside the generated artifact; treating their old pre-obligation scripts as
green proof discharges would be false.

Some directories contain only `GAP.md` and `source.txt`. Those are classified
proof gaps without a useful current proof attempt; do not add a fake proof just
to make the directory runnable.

The gap inventory is part of the harness. Run:

```sh
make -C otherTests/saw-core-lean gaps
```

From the repository root, the equivalent named target is:

```sh
make test-saw-core-lean-gaps
```

From this directory, the direct harness command is:

```sh
bash test.sh gaps
```

This validates that each proof-gap directory has an explicit local note and
reports proof/stress gaps separately from passing proof-discharge examples.

To work on one manually when it has a `proof.lean`, enter the subdirectory and
run:

```sh
bash ../../support/lean-proof-test.sh test
```
