# Proof Gap: Cryptol ChaCha20 Core Iterate

This directory preserves a large proof attempt for
`saw-boundary/cryptol_chacha20_core_iterate` (reclassified from drivers/ as an
expected `Prelude::Stream@core` rejection per the 2026-07-14 release 0.01
decision; the translation path folds into the OP-3 successor design). It is a
stress/proof-ergonomics gap,
not an accepted proof-backend regression.

The emitted obligation is useful because it exercises a large whole-Cryptol
ChaCha20 core term with recurrence/iteration structure. The proof attempt is
intended to be axiom-clean, but it currently exceeds the practical
elaboration/heartbeat budget under the default proof harness. Do not move this
back to `proofs/` until the generated obligation or proof script checks
reliably without heartbeat inflation, native-evaluation proof artifacts, or
backend-added automation.

2026-07-03 probe: the tracked large emitted artifact also fails to compile
because it references stale checked Nat div/mod helper names
`divNatChecked`/`modNatChecked`. That does not make this a proof-backend
candidate; it means any future work on this stress example must first refresh
and review the generated artifact, or reduce the helper-name drift to a small
litmus before treating it as a backend priority.

Next principled path: keep mining smaller emitted-obligation blockers into
focused differential or obligation rows, and defer the large proof itself to a
later proof-ergonomics/scalability phase.
