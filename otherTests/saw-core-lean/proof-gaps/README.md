# Proof Gaps

This directory keeps proof attempts and explicit proof-gap notes that are
useful stress cases but are not accepted backend proof regressions yet.

The default `proofs/` sweep is for obligations that elaborate and pass the axiom
audit under the current trust policy. BV-heavy crypto proofs currently live here
when they depend on `bv_decide`/`bv_check` native-evaluation axioms or time out
under checked automation. Keeping them out of `proofs/` prevents the default
regression suite from treating native-axiom or unavailable automation as a green
proof-discharge path.

Small proof examples can also live here when the backend now emits a sound
proof-carrying obligation but the proof-support phase has not yet discharged
that obligation. For example, E4/E5 now expose checked vector bounds contracts
inside the generated artifact; treating their old pre-obligation scripts as
green proof discharges would be false.

Some directories contain only `GAP.md` and `source.txt`. Those are classified
proof gaps without a useful current proof attempt; do not add a fake proof just
to make the directory runnable.

To work on one manually when it has a `proof.lean`, enter the subdirectory and
run:

```sh
bash ../../support/lean-proof-test.sh test
```
