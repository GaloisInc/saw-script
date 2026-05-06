# Case Study E — u128 byte-by-byte equality

*2026-05-06.*

## What we tested

`drivers/llvm_eq_u128_verify/` — `eq_u128` from
`exercises/functional-correctness/u128/u128.c`:

```c
bool eq_u128(uint64_t x[2], uint64_t y[2]) {
    return !bcmp(x, y, 16);
}
```

The driver uses `llvm_unsafe_assume_spec` for `bcmp` (bytewise
inequality flag, the standard libc spec) and `llvm_verify`s
`eq_u128` against the Cryptol property `[x == y] : [1]`. The
goal is dispatched to Lean via `offline_lean`.

## Hypothesis tested

> Do `llvm_verify`-emitted memory-model artifacts (load/store,
> alloc, struct projection) translate cleanly?

(Long-term plan §3 Case E.)

## Result — emission elaborates; discharge needs more tactical work

The translator handles the memory-model lowering correctly — the
emitted `.lean` elaborates against the support library, and the
driver test passes. What's emitted:

- The Cryptol-side `[x == y] : [1]` lifts through the assumed
  `bcmp` spec to a 16-byte comparison: 16 nested `gen 8 Bool` byte
  extractions from `x` and `y` (slicing the 128-bit input into 16
  byte-chunks at offsets 0, 8, 16, …, 120), each compared via
  `bvEq 8`, combined via `foldr Bool 16 …`, then re-encoded
  through `gen 32 Bool …` + `coerce` (Cryptol's type-level
  cast) to a `Vec 32 Bool` to match the bcmp return type.
- The C-side: a single 1-bit `bvEq 128 x y` result.
- Both sides should equal the same 1-bit boolean.

**Discharge attempt:** A simple `rw [bvEq_true_iff_BitVec_eq];
bv_decide` fails: `bv_decide` abstracts the entire LHS as an
opaque variable because Cryptol's `coerce`/`gen`/`foldr`/
`atWithDefault` aren't bv-decidable primitives.

**Aggressive simp + bv_decide** (`simp only [coerce, atWithDefault,
gen, ltNat, addNat, subNat, ite, foldr, Vector.getElem_ofFn]`)
times out at whnf — same `Vector.ofFn` cartesian-blowup we saw in
Case D. With 16 bytes × 8 bits + a `gen 32` and a `foldr 16`, the
nested `Vector.ofFn` materialization exceeds the default 200K
heartbeats.

## What this implies

**Not a SAW translation issue** — the emission is faithful to the
Cryptol semantics. **Not a soundness issue** — the goal is
expressible and well-formed.

**It's a tactical-library gap.** The same `Vector.ofFn` whnf cost
that motivated `atWithDefault_gen_lt` / `atWithDefault_genFix_lt`
in Case D also affects Case E, but the byte-array slicing pattern
needs different peelers than the genFix-comprehension pattern.
Specifically, the discharge would benefit from:

1. **Byte-extraction peeler.** A lemma of shape:

   ```lean
   theorem byteExtract_eq_slice (x : Vec 128 Bool) (offset : Nat) (h : offset + 8 ≤ 128) :
     gen 8 Bool (fun i => atWithDefault 128 _ d (gen 128 _ (atWithDefault 128 _ d x))
                            (offset + i))
     = x.extract offset 8
   ```

   Reduces a 16-deep byte-extraction to a single `extract` operation
   that `bv_decide` can handle.

2. **`foldr Bool` fold equation.** A lemma showing that
   `foldr Bool Bool 16 (fun b1 b2 => ite Bool b1 b2 false) true v`
   equals `Vector.foldr (· && ·) true v` or equivalently
   `(BitVec.toNat v.toBitVec) = (2^16 - 1)` for the Bool-AND fold.

3. **`coerce` simplification.** A simp-set rule that collapses
   `coerce α α (Eq.refl _) v = v` for same-type coercions.

These belong to the **§4.4 saw_simp / saw_decide library** work
(task #131), which is in the plan but not yet started.

## Driver kept; proof deferred

The driver `drivers/llvm_eq_u128_verify/` is committed with its
`.log.good` and `.lean.good` — it pins the memory-model emission
shape as a regression target. If the translator changes the
lowering of `unsafe_assume_spec`-based goals or the byte-array
slicing pattern, the `.lean.good` diff catches it.

The discharge waits on §4.4 tactical infrastructure — once
`saw_decide` (or equivalent peelers) lands, the proof.lean for
this case becomes a few lines.
