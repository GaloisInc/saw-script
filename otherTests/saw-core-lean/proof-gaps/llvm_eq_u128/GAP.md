# Proof Gap: LLVM eq_u128 (128-bit byte-decomposition memory-model compare)

The `workflows/llvm_eq_u128_verify` row emits the obligation comparing the
LLVM `eq_u128` result against the Cryptol spec `[x == y] : [1]`, mediated by
an `llvm_unsafe_assume_spec` for `bcmp` whose spec reads the two 128-bit
operands as `[16][8]` byte arrays and returns `zext`32`` `[s1 != s2]`.

It is NOT dischargeable under the current trust policy and support library.
Two independent facts block it; the second is decisive.

## 1. The emitted `goal` needs the completed-outline workflow (not a blocker)

`def goal` carries 66 embedded `h_bounds_` obligations (byte-loop array-index
bounds for `atWithProof_checkedM`/`atRuntimeCheckedM`) and one
`h_unsafeAssert_` obligation (a `Num`-coerce `Eq`), each emitted as
`by <tactics>; all_goals sorry`. A plain `proofs/` row is therefore
impossible — the harness rejects any emitted `sorry` outside the single
`goal_holds := by sorry` stub.

This part is easy: the generated `(first | assumption | omega |
(simp only [...macros...] ; omega) | skip)` closes every one of those
obligations on its own. Stripping the `; all_goals sorry` fallback (and
removing the trailing `goal_holds` stub) yields a `completed.lean` outline
that compiles clean, sorry-free, and defeq (proof-irrelevant) to the
generated `goal`. So a `completed.lean` is available for whoever discharges
the top-level equivalence; the bounds are not the problem.

## 2. The equivalence obligation does not reduce under checked automation (decisive)

The obligation (2661 emitted lines; ~246K-char elaborated goal after
`intro x y`) is a 128-bit byte-decomposition monadic tower in `Except String`:

    Bind.bind
      (iteM (Vec 1 Bool)
        (bvEq 32 (bvNat 32 0) <bcmp>)          -- bcmp == 0 ?
        (pure (bvNat 1 1)) (pure (bvNat 1 0)))  -- -> [1] / [0]
      (fun r_impl => Bind.bind
        (vecSequenceM 1 Bool #v[pure (bvEq 128 x y)])  -- spec side
        (fun r_spec => pure (bvEq 1 r_impl r_spec)))
    = pure Bool.true

where `<bcmp>` is `genWithBoundsM 16` byte loops, each an inner 8-bit
`genWithBoundsM`/`foldrM` that compares `atWithProof_checkedM 128 Bool x i …`
against the `y` bit at the same position (16 bytes x 8 bits = all 128 bits).

No support-library simp set reduces this `genWithBoundsM` / nested `foldrM` /
`atWithProof_checkedM` tower to a closed form. A full-goal `simp` must
traverse the entire ~246K-char tree and is pathologically slow. Measured on
this row's completed outline (leanprover v4.29.1):

  - full unfolding `simp only [iteM, foldrM, genWithBoundsM,
    atWithProof_checkedM, atRuntimeCheckedM, vecSequenceM, Vector.ofFnM,
    Bind.bind, Pure.pure, Except.bind, Except.pure, bvEq_refl]` with
    `maxHeartbeats 1000000` — does not terminate (elaboration still running
    after >240s);
  - targeted monadic `simp only [Bind.bind, Except.bind, Pure.pure,
    Except.pure, vecSequenceM_singleton_ok]` — >300s wall-clock, no result;
  - even a single `simp only [Bind.bind, Except.bind]` with the default
    `maxHeartbeats 200000` — >250s wall-clock, no result.

Per project policy the heartbeat budget was NOT raised to paper over this:
the timeout means the tactic plan is wrong, not that the budget is too small.
The right fix is support-library reduction lemmas, not brute-force simp.

## 3. Missing byte->word reconstruction bridge (secondary)

Even if the tower reduced, the crux identity is

    foldr-AND over 16 per-byte (bvEq 8 (byte_b x) (byte_b y)) = bvEq 128 x y

a byte-decomposition of 128-bit equality. Case-splitting on `bvEq 128 x y`:
the `x = y` branch is reflexive (`bvEq_refl` per byte after `subst`), but the
`x != y` branch needs the reconstruction `(forall byte b, byte_b x = byte_b y)
-> x = y`. The bit-extensionality primitives already exist
(`getMsbD_vecToBitVec_lt`, `BitVec.eq_of_getMsbD_eq` in
`SAWCoreBitvectors_proofs.lean`), so this bridge is buildable, but there is no
`bvEq_128_eq_foldr_bvEq8` / byte-decomposition lemma in the support library
today. (Candidate for the proof-support backlog.)

## Next principled path

1. Add support-library reduction lemmas that collapse the emitted
   `genWithBoundsM n` / nested `foldrM` / `atWithProof_checkedM` byte-loop
   shape to a closed `Vector.ofFn`/`gen` form using targeted `conv`/rewrite
   lemmas keyed on the emitted shape — NOT a full-tree `simp` (which times
   out). This is the prerequisite that unblocks reduction.
2. Add a checked `bvEq (8*k) a b = foldr-AND of per-byte (bvEq 8 …)`
   decomposition bridge (provable from the existing `getMsbD_vecToBitVec_lt`
   + `BitVec.eq_of_getMsbD_eq` extensionality lemmas).
3. Then the equivalence is dischargeable under the trust policy
   (no `bv_decide`/`bv_check`/`native_decide`, standard + Vec/BitVec
   round-trip axioms only).

No `proof.lean` is preserved here: no partial attempt reaches a useful
intermediate state (every reduction attempt times out before producing a
reduced goal), so there is nothing worth keeping per the proof-gaps README.
