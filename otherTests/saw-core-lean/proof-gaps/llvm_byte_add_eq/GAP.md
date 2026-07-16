# Proof gap: byte-decomposed addition vs bvAdd (W2 opener discharge)

`workflows/llvm_byte_add_verify` act 3 punts the straight-line 4-byte
carry-chain adder's correctness (`mp_add_simple a b == a + b`) to
Lean: a single 4001-line goal whose content is exactly the W2
byte-decomposition lemma family — `bvShl`/`bvShr` byte extraction,
8→16/32-bit zero-extension towers, truncation, per-byte `bvAdd` with
carry propagation, and the final `bvOr` byte reassembly, over a
symbolic 32-bit pair. No rotates, no multiplies, no recurrences —
the scouted gentlest entry to the BV wall (post-scout note: the
ORIGINAL SV-COMP body's na/nb early-exit logic explodes emission to
~700K lines; the straight-line adder carries the same lemma content
at 4K).

Status 2026-07-16: row landed GREEN (SMT refutes the seeded SV-COMP
carry bug on the original; SMT verifies the fixed and simple adders;
emission elaborates). The Lean discharge is NOT yet attempted — it
is the W2 proof-support library's seeding task, expected to produce
the reusable byte-split/carry lemma set (the same family eq_u128's
GAP.md names as its first missing block). Trust policy unchanged: no
bv_decide/bv_check/native_decide, no heartbeat bumps.
