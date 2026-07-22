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
    it directly targets the dominant cost — each per-word close is bounded and
    well under budget on its own.

Neither is a soundness concern; both are budget/packaging. The preserved
`completed.lean` + `proof.lean` are the real, checked (just over-budget)
artifacts, kept here so the gap is visible and not a silent skip.

## 2026-07-21 measurement update: cost model corrected; per-word split REFUTED

Controlled measurements (idle-ish box, Lean v4.29.1, `set_option profiler
true`, scratch variants of this row's `completed.lean`) invalidate the cost
attribution above and with it the "PRINCIPLED" unlock path:

    variant                                            user CPU   kernel check
    Z:  def goal + library, goal_holds := sorry          5.6 s     ~0
    A:  scaffold (big simp+apply+expand+refine),
        all 16 word closes sorried                      80.8 s     111-123 s*
    B:  scaffold + ONE word closed for real             80.8 s     (== A)
    K1: big simp only, then sorry                          —        78.4 s

    * profiled clean run: simp elaboration 1.16 s + 0.18 s; the rest is
      KERNEL type-checking of the produced proof term.

Consequences:

  * The per-word `ac_rfl` closes are FREE (B - A ~ 0 s), not the dominant
    cost. Splitting them into 16 independently-budgeted lemmas moves ~0 s
    out of the critical process. The "~206 s is the discharge tactic"
    attribution above conflated elaboration with kernel checking: the
    tactic block elaborates in ~2 s; the cost is the KERNEL CHECK of the
    normalization `Eq.mpr`/congruence chain (78 s for the big simp step,
    ~45 s for the Fin-expansion/refine tail).
  * The earlier 134-213 s full-compile swings were load noise around a
    ~112-135 s CPU-bound kernel check, consistent with the 109.8 s best
    run recorded above.
  * Staging the propositional rewrites out of the big simp does NOT work
    as-is: with `rotl_7/9/13/18` removed from the set, the first `simp
    only` itself dies with a whnf heartbeat timeout (the rotl collapse is
    load-bearing for the normalization's termination), so the rotl steps
    cannot simply be deferred to the post-normalization (small-motive)
    goal. Verified for both "second simp" and "rotl inside per-word
    closes" stagings.

Remaining honest unlock paths (neither is quick packaging; neither blocks
0.02 exit criteria — re-parked 2026-07-21):

  1. KERNEL-COST SURGERY: root-cause the 646 ms-elab / 78 s-kernel blowup
     of the big simp's proof chain (suspects: congruence motives over the
     zeta-expanded emitted term; kernel re-reduction of motive types) and
     restructure the normalization to be kernel-cheap — e.g. defeq-staging
     via `show` against an explicit bvOr/bvShl/bvShr mid-form so that only
     the 32 rotl rewrites remain propositional, over the SMALL normalized
     term.
  2. EXPLICIT MID-FORM MULTI-PROCESS SPLIT: extract the intermediate goal
     by trace, state it explicitly, and prove `goal -> mid` and
     `mid -> done` in separate files, each under the per-process cap
     (requires multi-unit proof staging in the harness; mechanical but
     heavy — pretty-printer round-trip fragility on ~10^2 KB statements).
  3. SAW-SIDE COMPOSITIONAL SPLIT (user suggestion 2026-07-21; likely the
     CHEAPEST path — try FIRST): this row deliberately verifies with NO
     overrides, which is what inlines both ladder stages into one
     monolithic goal. But `columnround` and `rowround` are each already
     verified as green rows, so a compositional driver (`llvm_verify`
     with those two results as overrides) emits the doubleround
     obligation at COMPOSITION granularity — spec-vs-spec at the stage
     boundary, no inlined quarterround arithmetic. Cryptol's doubleround
     IS rowround . columnround, so the residual obligation should be
     near-structural. Note this does not abandon the in-ITP decomposition
     pattern — it stacks SAW's own compositional machinery ON TOP of the
     two in-ITP-verified stage rows, which is exactly how the pattern was
     meant to scale. Requires: a new compositional workflow row + its
     discharge; the existing no-override row would then be re-scoped as
     the depth-scaling stress pin it already is.
