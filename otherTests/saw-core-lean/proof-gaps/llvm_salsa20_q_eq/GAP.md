# Proof Gap: LLVM Salsa20 Quarterround

This directory preserves a proof attempt for
`drivers/llvm_salsa20_q_verify`. It is a BV-heavy stress/proof gap, not an
accepted proof-backend regression.

The proof uses checked bridge lemmas to reduce the emitted vector-side
bitvector expression to a pure `BitVec` equation, then currently closes that
last equation with `bv_decide`. Under the current trust policy, completed
accepted proofs must not depend on `bv_decide`, `bv_check`,
native-evaluation proof artifacts, or proof-local native axioms.

Next principled path: keep the emitted obligation and proof attempt available
as a stress case, but only promote this row after the final 32-bit BV identity
has a checked Lean proof under the accepted trust policy.
