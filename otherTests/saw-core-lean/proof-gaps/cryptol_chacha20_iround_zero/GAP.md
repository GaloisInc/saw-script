# Proof Gap: Cryptol ChaCha20 Iround Zero

This directory preserves a large proof attempt for
`saw-boundary/cryptol_chacha20_iround_zero` (reclassified from drivers/ as an
expected `Prelude::Stream@core` rejection per the 2026-07-14 release 0.01
decision; the translation path folds into the OP-3 successor design). It is a
stress/proof-ergonomics gap,
not an accepted proof-backend regression.

The target proof reduces an emitted Cryptol iteration at index zero and then
proves the resulting bitvector equality. The proof attempt is intended to be
axiom-clean, but it currently exceeds the practical elaboration/heartbeat
budget under the default proof harness. Do not move this back to `proofs/`
until the generated obligation or proof script checks reliably without
heartbeat inflation, native-evaluation proof artifacts, or backend-added
automation.

Next principled path: keep the emitted recurrence/stream obligation visible,
extract smaller blockers when the proof exposes them, and defer the large proof
itself to a later proof-ergonomics/scalability phase.
