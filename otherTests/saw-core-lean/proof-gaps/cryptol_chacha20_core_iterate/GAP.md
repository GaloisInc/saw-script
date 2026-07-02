# Proof Gap: Cryptol ChaCha20 Core Iterate

This directory preserves a large proof attempt for
`drivers/cryptol_chacha20_core_iterate`. It is a stress/proof-ergonomics gap,
not an accepted proof-backend regression.

The emitted obligation is useful because it exercises a large whole-Cryptol
ChaCha20 core term with recurrence/iteration structure. The proof attempt is
intended to be axiom-clean, but it currently exceeds the practical
elaboration/heartbeat budget under the default proof harness. Do not move this
back to `proofs/` until the generated obligation or proof script checks
reliably without heartbeat inflation, native-evaluation proof artifacts, or
backend-added automation.

Next principled path: keep mining smaller emitted-obligation blockers into
focused differential or obligation rows, and defer the large proof itself to a
later proof-ergonomics/scalability phase.
