# Proof Gap: LLVM Salsa20 doubleround (in-ITP decomposition, double depth)

This directory preserves the in-ITP decomposition discharge of the
`s20_doubleround` obligation emitted by
`workflows/llvm_doubleround_itp` (verified with NO overrides, so both the
columnround and rowround stages — eight quarterrounds in two ladder stages —
inline into ONE goal over a single [16][32] state).

## The gap is wall-clock budget, NOT a resisting subgoal

This is an unusual gap: the discharge is COMPLETE and VALID. `completed.lean`
here is the two-level analogue of `proofs/llvm_rowround_itp/completed.lean`
and `proofs/llvm_columnround_itp/completed.lean`, and it REUSES their proof
machinery verbatim:

  * the lemma library (`rotl_shlor_32`, `rotl_7/9/13/18`, `seq4/seq16`,
    `foldr_ofFn_all_true`, the `bvtn_*` shift constants) is byte-for-byte
    identical to the single-round rows — the rotate amounts {7,9,13,18} and
    the sequence widths {4,16} are invariant under ladder depth; and
  * the `goal_holds` tactic script is identical in form: `simp only` reduces
    the monadic scaffolding, `apply foldr_ofFn_all_true` splits into 16
    per-word `bvEq` goals, each pushed to `BitVec` and closed by `ac_rfl`.

No per-word `ac_rfl` resists; there is no `sorry`, no `bv_decide`, no bumped
`maxHeartbeats`. `completed.lean` elaborates to a valid, axiom-clean proof
(only `propext` / `Classical.choice` / `Quot.sound` and the two vec<->BitVec
round-trip axioms — the same allowlist the columnround row passes under the
harness audit; the doubleround proof term differs only in size).

The single blocker is the harness's fixed 120 s per-Lean-process cap
(`support/lake-timeout.sh`, `LAKE_TIMEOUT_SECS=120`). The doubleround
obligation's `def goal` is ~2x the single-round term (5462 emitted lines vs
2695; bvXor sites 32->80, bvAdd 32->64, atWithProof 50->98, vecSequenceM
literals 10->19), and its complete discharge does not fit the budget:

    row                             fallback tactic      real compile time
    rowround   (single, 50 bounds)  simp ... at *        102.2 s   (fits)
    doubleround (double, 98 bounds)  simp ... at *        188.9 s   (over)
    doubleround (double, 98 bounds)  simp ... <;> omega   134.4 s   (over)

## Cost attribution / scaling law

The cost is almost entirely the `goal_holds` TACTIC, not the term. A direct
isolation (independently measured while reconciling two concurrent builds of
this row) pins it: the generated `def goal` plus the lemma library, with
`goal_holds := sorry`, type-checks in ~7 s — so the ~2x-larger emitted term
and its 98 embedded index-safety bounds fallbacks are CHEAP to check. The
full verbatim discharge elaborates rc=0, sorry-free, in ~213 s in that same
run. Hence ~206 s is the discharge tactic: the `simp only` monadic reduction
plus the 16 per-word double-depth `ac_rfl` closes.

Within that tactic cost there is one secondary, removable component. The
emitted bounds fallback is `simp only [<macro lemmas>] at *; omega`; the `at
*` produces a bulky proof term at each of the 98 sites, and `goal_holds`'s
own `simp` then has to traverse those terms. Replacing the `at *` with a
goal-only `simp only [...] <;> omega` (a drift-safe completed-outline edit —
proof irrelevance keeps `goal` definitionally unchanged, and the harness's
completed-outline drift check enforces it) trims the `simp` traversal by
~55 s (188.9 -> 134.4 s in the full-compile measurements below). It does NOT
touch the dominant cost: the core `simp` reduction and the 16 double-depth
`ac_rfl` closes still run ~130 s, well over budget.

The verbatim discharge (`completed.lean` here) is right at the budget
boundary and swings across it with machine load: four compiles of the same
file measured 213 s, 188.9 s, 134.4 s (goal-only fallbacks), and 109.8 s
(verbatim, under `#print axioms`). Because the single-round row is ALREADY at
102 s, no fallback tuning brings the honest double-depth discharge robustly
under 120 s — a run that lands at 110 s locally is one busy CI box away from
190-210 s, so promoting it would make the gate flaky. This is the scaling
wall the two-level case study set out to probe: the in-ITP decomposition's
outer composition is depth-INVARIANT, but the per-word `ac_rfl` closes and the
`simp` reduction scale with the size of the inlined arithmetic, and at double
depth that tactic cost crosses the CI wall-clock cap.

## What would unlock promotion to a green `proofs/` row

The principled path is the second one below; the first only shaves the
secondary cost.

  * PARTIAL: a cheaper generator-emitted bounds discharge (goal-only
    `simp; omega`, or a direct decidability proof of each `k < 16 / k < 32`
    literal bound). This removes ~55 s but leaves the dominant ~130 s core
    `simp` + 16 `ac_rfl` cost, so it does not on its own fit 120 s.
  * PRINCIPLED: split the single monolithic obligation so the 16 per-word
    `ac_rfl` closes elaborate as 16 independently-budgeted lemmas rather than
    one 120 s process. The outer `foldr_ofFn_all_true` discharge is already
    depth-invariant, so this is a packaging change, not new mathematics, and
    it directly attacks the dominant cost — each per-word close is bounded and
    well under budget on its own.

Neither is a soundness concern; both are budget/packaging. The preserved
`completed.lean` + `proof.lean` are the real, checked (just over-budget)
artifacts, kept here so the gap is visible and not a silent skip.
