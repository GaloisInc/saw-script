# Proof Gap: LLVM ChaCha20 Quarterround

This directory preserves a proof attempt for
`workflows/llvm_chacha20_q_verify`. It is a BV-heavy stress/proof gap, not an
accepted proof-backend regression.

SCOPE (extended 2026-07-15): this gap also covers the EIGHT qround
obligations emitted by `workflows/llvm_chacha20_core_verify` — the
same quarterround equation at eight concrete (a,b,c,d) index tuples,
blocked by the identical bv_decide trust-policy constraint. One
policy-compliant discharge strategy for the qround equation unparks
all nine obligations at once.

The proof compares the LLVM quarterround output with the Cryptol specification.
The unchanged positions close by ordinary reflexive bitvector equality, but the
four quarterround equations still use `bv_decide` in the preserved proof
attempt. Under the current trust policy, completed accepted proofs must not
depend on `bv_decide`, `bv_check`, native-evaluation proof artifacts, or
proof-local native axioms.

Next principled path: keep the emitted obligation and proof attempt available
as a stress case, but only promote this row after the 32-bit BV equations have
checked Lean proofs under the accepted trust policy.
