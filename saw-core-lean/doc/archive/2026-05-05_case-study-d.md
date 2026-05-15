# Case Study D — fib-like comprehension at small width

*2026-05-05.*

## What we tested

`drivers/cryptol_running_sum_verify/RunningSum.cry` defines two
versions of the same function over `[8][32]`:

```cryptol
runningSumComprehension xs = sums ! 0
  where sums = [0] # [ s + x | s <- sums | x <- xs ]

runningSumNaive xs =
  xs@0 + xs@1 + xs@2 + xs@3 + xs@4 + xs@5 + xs@6 + xs@7
```

The driver dispatches `runningSumComprehension xs ==
runningSumNaive xs` to Lean via `prove_print (offline_lean …)`.

The first definition has the same `[seed] # [body | … <- self]`
self-referential-comprehension shape as popcount (Case B), but
with a different body (`s + x` instead of
`if elt then prev+1 else prev`). Phase 5 BoundedVecFold lowers it
to the same `genFix`-based emission.

## Hypothesis tested

> Is the popcount stall genuinely about the genFix shape, or
> specific to popcount's particular body?

(Long-term plan §3 Case D.)

## Result — hypothesis confirmed

The first attempt — push to BitVec via the @[simp]-tagged
bridges, then `bv_decide` — stalls **exactly the same way** as
Case B did:

```
error: The prover found a potentially spurious counterexample:
  - It abstracted the following unsupported expressions as
    opaque variables: [vecToBitVec…, vecToBitVec…, …]
```

`bv_decide` treats the `genFix`-shaped LHS as an opaque term
and gives up. With `+` as the body instead of `if`, the stall
is identical. **The blocker is shape-level, not body-specific.**

## What this implies for the plan

Stop condition for Case C+D in the long-term plan §3:

> After cases C+D (just two): we know whether the genFix issue is
> the dominant comprehension blocker. If yes, pivot to **§4.1
> Lean-side bridge library**.

The condition fires. Next move: §4.1 — prove a Lean-side
genFix-shape bridge lemma in `CryptolToLean.SAWCorePreludeProofs`
of approximately the form

```lean
theorem genFix_bounded_acc_eq_foldl
    {n : Nat} {α : Type} (seed : α) (f : α → β → α) (ext : Vec n β) :
    genFix … (the SAW emission shape) … = Vector.foldl f seed ext
```

(parameterized over the body shape — the goal is to express the
recurrence so that user proofs can `rw [genFix_bounded_acc_eq_foldl]`
and then `bv_decide` on the `Vector.foldl` form, which is concrete.)

This is the same bridge-library pattern that worked for the
rotation case (Case C): one general Lean-side theorem proved
once, applied by every comprehension case study afterwards. No
translator-side rewrites — the equivalence lives in the kernel-
checked proof, per the obvious-correctness principle (§2.4).

Once §4.1 lands, Case D's proof.lean should close cleanly via
`rw [genFix_bounded_acc_eq_foldl]; bv_decide`. Same for Case B
(popcount, task #141).

## Driver kept; proof deferred

The driver `drivers/cryptol_running_sum_verify/` is committed
with its `.log.good` and `.lean.good` — it pins the genFix
emission shape as a regression target. If the translator ever
changes the lowering shape (e.g., emits `Vector.foldl` directly,
which §4.5 explicitly rejects under §2.4), the `.lean.good`
diff will catch it.

The `proofs/cryptol_running_sum_eq/` discharge is **not** in
this commit; it will be added once §4.1 lands. Adding a
`sorry`-stub now would violate the project's no-sorry discipline
in the test suite.
