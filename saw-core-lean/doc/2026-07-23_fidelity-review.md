# Semantic-fidelity review: support-library primitive realizations

Date: 2026-07-23. Reviewer: independent session (Opus-class), fresh
context, read-only worktree; every public definition in the four
support-library files dispositioned against the SAW authorities
(`saw-core/prelude/Prelude.sawcore`, `cryptol-saw-core/saw/
Cryptol.sawcore`, `SAWCore/Simulator/{Prims,Concrete,Prim}.hs`).
Trigger: the same-day `bvToInt` soundness finding (see below) raised
the question "how many more of these exist?".

**Headline: no additional same-value soundness divergences.** One
ungated total-vs-partial edge (IntMod at n = 0, F1 below, OPEN) and
documented cosmetic notes. Every classic risk site was individually
verified faithful.

## Authority note (worth remembering)

The concrete simulator only OVERRIDES a subset of operations
(`Concrete.hs`); the base table is the SHARED `Prims.hs` constMap
(`Prims.hs:356-366`), which is the authority for the Rational family
and for `foldr`/`foldl`/`gen`/`zip`/`atWithDefault` and the
comparators. Rationals are stored UNREDUCED (numer, denom); all
observations are reduction-invariant (cross-multiplication,
floor-division), so Lean's reduced `Rat` agrees observationally.

## Findings

### F0 — `bvToInt` signed-vs-unsigned (FIXED same day, pre-review)

Found by a separate audit session; fixed in commit "SOUNDNESS FIX —
bvToInt" before this review ran; the review verified the fix and its
new sign-crossing differential coverage. Record: the library realized
both `bvToInt` and `sbvToInt` as `BitVec.toInt` (signed); SAW's
`bvToInt` is UNSIGNED (`Prelude.sawcore:2113`; `bvToIntOp = ...
unsigned`, `Concrete.hs`). Divergent on every sign-bit-set input; the
only pre-existing test case (0x7f) never crossed the sign bit. Zero
landed proofs were affected (nothing proved through `bvToInt`).

### F1 — IntMod at n = 0: ungated totalization (OPEN, low severity)

- Lean: the `IntMod` family routes through `Int.fmod _ n`, TOTAL at
  n = 0 (`fmod x 0 = x`).
- SAW: every concrete IntMod op computes Haskell ``x `mod` 0`` at
  n = 0 (`toIntModOp`, `Concrete.hs:295`; `intModBinOp`/`intModUnOp`)
  — a "divide by zero" CRASH; no SAW-observable `Z 0` value exists.
- The library's former section comment claimed SAW's n = 0
  convention is "no reduction" — FALSE; corrected same day.
- Unlike every division-family partial op (all gated by
  `_checked`/`_runtimeM` contracts), IntMod carries NO gate.
  Reachable only from raw SAWCore (Cryptol's `Z n` requires n ≥ 1).
- Pinned: `differential/intmod_zero_boundary` (known-gap row whose
  expected diagnostic is the SAW-side crash). Disposition
  (translation-time gate vs documented caveat) is an open user
  decision, tracked in TODO.md.
- For n ≥ 1 the fmod realization is exactly right, including
  negative representatives (verified both sides: `toIntMod 5 (-3)`
  = 2).

## Verified-correct subtle sites (confirmations)

- **Flipped-operand comparators** `bvugt/bvuge/bvsgt/bvsge`: Lean
  flips operands over `ult/ule/slt/sle`; matches `Prim.hs:216-223`
  argument order exactly (not just on symmetric inputs).
- **Int division/modulus**: `Int.fdiv`/`Int.fmod` vs SAW's Haskell
  `div`/`mod` — both floor; all four sign combinations checked;
  zero divisor gated.
- **Signed bv division**: `.sdiv`/`.srem` = toward-zero /
  dividend-sign = Haskell `quot`/`rem` (`Prim.hs:288-296`);
  most-negative/-1 wraps identically both sides.
- **`ecSMod` is signed REMAINDER, not modulus**: `Cryptol.sawcore:
  1330` defines it via `bvSRem`; the Lean route matches. (`%$` as
  sign-of-divisor smod would have been the classic error.)
- **Shifts**: `bvShl`/`bvShr` logical, `bvSShr` arithmetic —
  fill and direction match `Prim.hs:298-305`, including shift ≥
  width. Generic vector `shiftL`/`shiftR` match `vShiftL/vShiftR`
  (`Prims.hs:1247-1253`) algebraically, including i ≥ n and i = 0.
- **Rotates**: modular indexing matches `vRotateL/vRotateR`
  (`Prims.hs:1238-1245`), including by 0/n/multiples and n = 0.
- **`bvLg2`**: ceil-log2 with `lg2 0 = lg2 1 = 0` reproduces SAW's
  `lg2rem` semantics (`Prim.hs:342-352`) across powers and
  non-powers of two.
- **`widthNat`**: `log2 n + 1` (0 at 0) matches the Pos
  bit-recursion (`Prelude.sawcore:1158-1166`).
- **Bit counts**: popcount/clz/ctz directions (clz from MSB, ctz
  from LSB) and the all-zero → n boundary match `Prim.hs:225-240`;
  the `bvNat n` result encoding never truncates (count ≤ n < 2^n).
- **`zip` truncates to min length**; tuple encoding
  (right-nested-with-Unit) matches `vZipOp`.
- **`foldr`/`foldl` direction and argument order** match
  `Prims.hs:1269-1297`.
- **`iteM` laziness**: Lean is eager but DISCARDS the unselected
  branch's Except value, so an error in the not-taken branch never
  escapes — observationally identical to SAW's lazy `ite` (no ⊥
  representable in the carrier).
- **Conversions**: `bvNat` (mod 2^n), `intToBv` (two's complement
  for k < 0), `bvToNat` (unsigned), `sbvToInt` (signed), extensions
  `bvUExt`/`bvSExt` — all match, including wrap/oversize inputs.
- **Rational family**: reduction-invariant observations over SAW's
  unreduced pairs (`Prims.hs:1344-1476`); floor on negatives
  (-3/2 → -2), unreduced equality (2/4 = 1/2), negative
  denominators; zero-denominator gated.
- **`bytesToString`** (cosmetic caveat): bytes ≥ 128 may map to
  non-UTF8 scalars; used only for diagnostic error strings; ASCII
  path correct.

## Total-vs-partial ledger

| Op family | SAW partial at | Lean bare realization | Gate |
|---|---|---|---|
| divNat/modNat/divModNat | y=0 (crash) | total (Nat.div/mod = 0) | checked + runtimeM |
| intDiv/intMod | y=0 (crash) | total (fdiv/fmod) | checkedM + runtimeM |
| bvUDiv/bvURem/bvSDiv/bvSRem | y=0 | total (BitVec ops) | checkedM + runtimeM + ecS* width gates |
| ratio/rationalRecip | 0 (crash) | total (Rat, x/0=0) | checkedM + runtimeM |
| at (index OOB) | Prelude error string | — | atWithProof_checkedM / atRuntimeCheckedM (byte-exact message) |
| **IntMod ops** | **n=0 (crash)** | **total (fmod)** | **NONE — F1, open** |

## Per-definition disposition summary

Every public definition in `SAWCoreVectors.lean` (1),
`SAWCoreBitvectors.lean` (1), `SAWCorePreludeExtra.lean` (11), and
`SAWCorePrimitives.lean` (~130) was individually dispositioned:

- **FINDING**: the seven `IntMod` operations (F1, n = 0 only;
  correct for n ≥ 1).
- **NOT-CHECKED (out of scope, by design)**: the `Prelude.fix` and
  `MkStream` proof-obligation contract families
  (`saw_fix_*_raw`, `saw_fix_bounded*`, `saw_stream_*`,
  `saw_mkStream_*`) — these are obligation contracts, not
  same-semantics value realizations; their soundness arguments are
  the separately-audited OP-3/R3b records.
- **OK**: everything else, including the two bridge axioms
  (`vecToBitVec_bitVecToVec` / `bitVecToVec_vecToBitVec` — the
  documented two-axiom trusted base, mutually inverse), the
  `saw_unsafeAssert` discharge tactic (rfl/decide/omega only, no
  fabricated proofs), `saw_throw_error`, the string operations, and
  `coerce` (= `cast` over a genuine `Eq Type` proof).

The full per-definition table (file:line per def) is preserved in
the reviewing session's transcript; this document records the
dispositions and every non-OK item in full.

## Relation to the differential edge-case matrix (same day)

The 200+-case labeled differential matrix
(`differential/{bitvector_conversions,bitvector_arithmetic,
bitvector_division,bitvector_bitwise_shift,bitvector_order_width,
nat_scalar,int_scalar,int_div_mod,intmod_scalar,rational_scalar}`)
executably pins most of the confirmations above — one
SAW-vs-Lean observation line per case, so any regression in these
semantics names the exact case. The review and the matrix were
produced independently and agree: one open item (F1), zero
additional divergences.
