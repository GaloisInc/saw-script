/-
Case Study — LLVM Tuple Swap: Lean discharge of a tuple-structured
memory postcondition.

  intTests/test_llvm_tuple/test.c (LLVM `swap` over struct.triple)
       │
       │  llvm_verify against Cryptol's `swap_spec (xs,y,z) = (reverse xs, z, y)`
       ▼
  workflows/llvm_tuple_swap/test_llvm_tuple_swap.saw
       │
       │  (offline_lean) emits the nested-PairType equality obligation
       ▼
  workflows/llvm_tuple_swap/test_llvm_tuple_swap.swap_LLVM_points-to0.lean
       │
       │  the generated outline carries `atWithProof_checkedM` bounds
       │  evidence inside `goal`, so we complete the OUTLINE (completed.lean),
       │  removing the emit-stage `sorry` fallbacks and proving `goal_holds`.
       ▼
  proofs/llvm_tuple_swap_eq/proof.lean    ←  YOU ARE HERE (replays it)

The emitted goal is the componentwise equality of two nested tuples
over a symbolic `x : ([4][8],[16],[16])`:

  ( reverse x.0, x.2, x.1 )  ==  ( [x.0@3, x.0@2, x.0@1, x.0@0], x.2, x.1 )

They agree once the spec-side reverse indices `3 - (3 - i)` normalize
to `i` and each componentwise `bvEq` over identical components reduces
via `bvEq_refl`. This is the tuple/record-structured analogue of the
`demoProbe/eq` reverse discharge, extended across the nested `PairType`
projections. The completed outline (completed.lean) proves `goal_holds`
sorry-free; this file replays it as `goal_closed`.

Axiom audit: depends only on the allowlisted `propext`,
`Classical.choice`, `Quot.sound` (from `simp`/`decide`) — no `sorryAx`,
no `bv_decide`/`native_decide` native axioms.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
