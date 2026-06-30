# Proof Gaps

This directory keeps proof attempts that are useful stress cases but are not
accepted backend proof regressions yet.

The default `proofs/` sweep is for obligations that elaborate and pass the axiom
audit under the current trust policy. BV-heavy crypto proofs currently live here
when they depend on `bv_decide`/`bv_check` native-evaluation axioms or time out
under checked automation. Keeping them out of `proofs/` prevents the default
regression suite from treating native-axiom or unavailable automation as a green
proof-discharge path.

To work on one manually, enter the subdirectory and run:

```sh
bash ../../support/lean-proof-test.sh test
```
