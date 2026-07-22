# Proof cookbook: discharging translated SAW goals in Lean

*Phase 7 / Phase 9 — 2026-05-03.* Worked-examples companion to
[`getting-started.md`](getting-started.md). Each pattern below
maps a class of Cryptol-emitted goal shape to a discharge tactic
that closes it.

For background on the support library architecture, see
[`architecture.md`](architecture.md). For the full theorem list,
read
[`lean/CryptolToLean/SAWCoreBitvectors_proofs.lean`](../lean/CryptolToLean/SAWCoreBitvectors_proofs.lean).

## Pattern 1: concrete-input bv arithmetic

**Shape:** `bvAdd 8 (bvNat 8 5) (bvNat 8 3) = bvNat 8 8`

**Discharge:** `by decide`.

```lean
import CryptolToLean
open CryptolToLean.SAWCorePrimitives

example : bvAdd 8 (bvNat 8 5) (bvNat 8 3) = bvNat 8 8 := by decide
example : bvSub 8 (bvNat 8 10) (bvNat 8 4) = bvNat 8 6 := by decide
```

**Why it works.** Every bv op is a `noncomputable def` routing
through `Lean.BitVec`. With concrete arguments, the whole
expression reduces; `decide` checks the resulting proposition.
When `decide` stalls, `simp only` with the relevant `vecToBitVec_*`
round-trip lemmas plus the op's defining equations makes simp-style
progress (see Pattern 2).

## Pattern 2: bv arithmetic identities (symbolic)

**Shape:** `bvAdd 8 x y = bvAdd 8 y x` for symbolic `x, y`.

**Discharge:** apply the corresponding theorem from
`SAWCoreBitvectorsProofs`.

```lean
import CryptolToLean
open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

example (x y : Vec 8 Bool) : bvAdd 8 x y = bvAdd 8 y x :=
  bvAdd_comm 8 x y

example (x y z : Vec 8 Bool) :
    bvAdd 8 (bvAdd 8 x y) z = bvAdd 8 x (bvAdd 8 y z) :=
  bvAdd_assoc 8 x y z

example (x : Vec 8 Bool) : bvXor 8 x x = bvNat 8 0 :=
  bvXor_same 8 x

example (x : Vec 8 Bool) : bvAdd 8 (bvNat 8 0) x = x :=
  bvAdd_id_l 8 x
```

**Available theorems** (selection — see the file for the full
list):

| Identity | Theorem |
|---|---|
| `x + 0 = x` | `bvAdd_id_r` |
| `0 + x = x` | `bvAdd_id_l` |
| `x + y = y + x` | `bvAdd_comm` |
| `(x + y) + z = x + (y + z)` | `bvAdd_assoc` |
| `x - 0 = x` | `bvSub_n_zero` |
| `0 - x = -x` | `bvSub_zero_n` |
| `x - y = x + -y` | `bvSub_eq_bvAdd_neg` |
| `-(x + y) = -x + -y` | `bvNeg_bvAdd_distrib` |
| `x ^ x = 0` | `bvXor_same` |
| `x ^ 0 = x` | `bvXor_zero` |
| `(x ^ y) ^ z = x ^ (y ^ z)` | `bvXor_assoc` |
| `x ^ y = y ^ x` | `bvXor_comm` |
| `bvEq x x = true` | `bvEq_refl` |
| `bvEq x y = bvEq y x` | `bvEq_sym` |
| `bvEq x y = true ↔ x = y` | `bvEq_iff` |

## Pattern 3: bv equality via subtraction

**Shape:** `a = b ↔ bvSub w a b = intToBv w 0`

**Discharge:** `bvEq_bvSub_l` / `bvEq_bvSub_r`.

```lean
example (w : Nat) (x y : Vec w Bool) (h : bvSub w x y = intToBv w 0) :
    x = y :=
  (bvEq_bvSub_l w x y).mpr h
```

## Pattern 4: signed comparison predicates

**Shape:** `isBvslt w a b → isBvsle w a b` (signed strict-less
implies signed less-or-equal), and similar.

**Discharge:** apply named theorems.

```lean
example (w : Nat) (a b : Vec w Bool) (h : isBvslt w a b) :
    isBvsle w a b :=
  isBvslt_to_isBvsle w a b h

example (w : Nat) (a b : Vec w Bool) (h : isBvule w a b)
    (h2 : isBvslt w a (intToBv w 0)) :
    isBvslt w b (intToBv w 0) :=
  bvule_to_bvslt_zero w a b h h2
```

**Available signed predicate theorems**:

| Statement | Theorem |
|---|---|
| `isBvslt a b → isBvsle a b` | `isBvslt_to_isBvsle` |
| `isBvult a b → isBvule a b` | `isBvult_to_isBvule` |
| `isBvule a b → isBvult a b ∨ a = b` | `isBvule_to_isBvult_or_eq` |
| `isBvslt a b → bvEq a b = false` | `isBvslt_to_bvEq_false` |
| `¬ isBvslt a a` | `isBvslt_antirefl` |
| `isBvsle a b → isBvsle b a → a = b` | `isBvsle_antisymm` |
| `¬ isBvslt a (bvsmin w)` | `not_isBvslt_bvsmin` |
| `¬ isBvslt (bvsmax w) a` | `not_isBvslt_bvsmax` |
| `isBvule (intToBv w 0) a` | `isBvule_zero_n` |
| `¬ isBvult a (intToBv w 0)` | `isBvult_n_zero` |
| `isBvult a b → isBvule (a + 1) b` | `isBvult_to_isBvule_suc` |
| `isBvslt a b → isBvsle (a + 1) b` | `isBvslt_to_isBvsle_suc` |

## Pattern 5: SAW `ite`/`iteDep` collapse

**Shape:** `iteDep p (Bool.true) fT fF = fT` and similar.

**Discharge:** `simp` (the `iteDep_True`, `iteDep_False`, and
`ite_True`, `ite_False` lemmas in
`CryptolToLean.SAWCorePreludeExtra` are tagged `@[simp]`).

```lean
example (fT fF : Bool) :
    CryptolToLean.SAWCorePreludeExtra.ite Bool true fT fF = fT := by simp
```

## Pattern 6: Bool case-split (the walkthrough pattern)

**Shape:** Cryptol property over `Bit` parameters that reduces
to `(a && b) || (a && c) == a && (b || c)` — i.e., a finite-state
universally-quantified Bool property.

**Discharge:** `intro …; cases … <;> cases … <;> rfl`.

```lean
theorem distrib (a b c : Bool) :
    (CryptolToLean.SAWCorePreludeExtra.ite Bool
      (CryptolToLean.SAWCorePreludeExtra.ite Bool a b Bool.false)
      Bool.true
      (CryptolToLean.SAWCorePreludeExtra.ite Bool a c Bool.false))
    = (CryptolToLean.SAWCorePreludeExtra.ite Bool a
         (CryptolToLean.SAWCorePreludeExtra.ite Bool b Bool.true c)
         Bool.false) := by
  cases a <;> cases b <;> cases c <;> rfl
```

End-to-end test: `otherTests/saw-core-lean/proofs/walkthrough/proof.lean`.

## Pattern 7: Recursive fixed-point obligations

**Shape:** a generated proposition such as
`saw_fix_unique_exists α body`.

**Discharge:** prove the emitted contract in Lean. Small cases may close
by unfolding the literal body and proving uniqueness directly; larger
cases should use Lean-side recurrence lemmas or tactics whose generated
proof terms are kernel checked.

Do not rely on old structural helper names in proof scripts. Those helper
surfaces were removed because they encoded semantic recurrence reasoning
outside the generic proof-carrying contract.

## Pattern 8: `vecToBitVec` round-trip rewrites

**Shape:** when working with `BitVec` lemmas, you may end up
with subterms `vecToBitVec (bitVecToVec bv)` or
`bitVecToVec (vecToBitVec v)` that should reduce.

**Discharge:** `rw [vecToBitVec_bitVecToVec]` /
`rw [bitVecToVec_vecToBitVec]`. These are the 2 Phase 9 coherence
axioms documenting that the converters are mutual inverses;
they're decidable per concrete width via `by decide` if you
want to spot-check.

```lean
example (n : Nat) (bv : BitVec n) :
    vecToBitVec (bitVecToVec bv) = bv :=
  vecToBitVec_bitVecToVec bv
```

## Pattern 9: checked wrapped-helper bridges

**Shape:** generated Phase-beta goals often contain eager `Except` helpers such
as `genM`, `atWithDefaultM`, `vecSequenceM`, `foldrM`, and `foldlM`.

**Discharge:** use bridge lemmas only after proving the explicit success
premises. For example, `vecSequenceM_ok_of_get` and
`atWithDefaultM_vecSequenceM_ok_lt` require success for every vector element,
and `foldrM_pure_eq_foldr` / `foldlM_pure_eq_foldl` require a checked pure-step
equation. These lemmas intentionally do not hide `Except.error` or pretend that
eager helpers are lazy.

End-to-end test for the bridge-lemma patterns:
`otherTests/saw-core-lean/support-lemmas/cookbook/proof.lean`.

## Lifting SAW-typed goals to `BitVec`

There is no convenience-tactic module today (a `CryptolToLean.Tactics`
layer is a candidate proof-ergonomics addition; audit 2026-07-14
removed the description of one that never existed). The manual
recipe that layer would package:

1. `simp only [<the bv ops in your goal>]` to unfold the SAW-named
   primitives to their `BitVec` routings;
2. rewrite with the `vecToBitVec_*` round-trip lemmas
   (`SAWCoreBitvectors_proofs.lean`) to reach a pure `BitVec n`
   goal;
3. Check with checked `BitVec` lemmas, `simp`, `omega`, or `grind`
   under the trust policy below.

## Bitvector automation trust policy (TWO TIERS, 2026-07-21)

**Strict tier (the default).** Accepted proofs depend on nothing beyond the
Lean kernel's three built-in axioms and the two Vec<->BitVec round-trip
axioms. Do not use plain `bv_decide` or `bv_check` in strict-tier rows. They
are powerful and use LRAT certificates, but the current Lean frontend checks
those certificates through native evaluation and inserts a proof-local native
axiom (`<decl>._native.bv_decide.ax_*`) for substantial goals. That widens
the trusted base to Lean code generation. Use checked Lean proof automation
instead: named `BitVec` lemmas, the SAW bitvector bridge lemmas, `simp`,
`grind`, `omega`/`bv_omega` where applicable, and hand-written helper
theorems.

**`native-eval` tier (per-row opt-in, user decision 2026-07-21).** A
conformance row may carry a `.trust-tier` file containing `native-eval`;
that row's axiom audit additionally admits `bv_decide`'s per-invocation
proof-local native axioms — and NOTHING else (`sorryAx` and arbitrary
axioms are still rejected). Mechanics, all enforced by
`replay/axiom-audit.awk` (the single audit authority) plus both harness
consumers:

  * the tier is printed loudly on every run, with the recorded
    resolution note;
  * an unknown tier name fails (`UNKNOWN-TRUST-TIER`);
  * a stale marker — a tier row whose proof uses no bv_decide native
    axiom — fails (`TRUST-TIER-UNUSED`);
  * proof-side files must not DECLARE axioms or macro/elab machinery
    (source lint; closes the forged-axiom-name hole that a
    pattern-based allowance would otherwise open);
  * `support/trust-tier-selftest.sh` mutation-tests all four failure
    modes on every conformance run.

RESOLVE LATER (recorded): the tier exists because lean-smt's cvc5 BV proof
reconstruction is not yet usable (2026-07-21 probe: its own BitVec tests
leave admitted placeholders; ~30% of cvc5 proof rules reconstruct). When it
lands upstream, tier rows migrate to the strict tier by swapping
`bv_decide` -> `smt` and deleting `.trust-tier` — the row proofs are
structured to make that a one-token change.

If a bitvector obligation cannot be discharged under either tier's rules,
leave it as an explicit proof obligation or mark the example as an expected
proof gap. The emitted obligation is still meaningful and sound; only the
automation is missing.

## When the cookbook doesn't have your pattern

If your goal doesn't match any pattern above:

1. **Reduce manually.** `unfold bvAdd bvSub …` to expose the
   underlying `BitVec` ops, then apply Lean's `BitVec` library
   lemmas. The `vecToBitVec_bvAdd` / `vecToBitVec_bvSub` / etc.
   helpers in `SAWCoreBitvectors_proofs.lean` automate the
   common rewrites.

2. **Try checked automation.** For concrete-width or structurally simple
   goals, lift to `BitVec` with `congrArg vecToBitVec` and the
   `vecToBitVec_*` round-trip lemmas, then
   try `simp`, `grind`, `omega`/`bv_omega`, and named `BitVec` lemmas. Avoid
   `bv_decide` in strict-tier proofs; for genuinely SAT-shaped fixed-width
   goals a row may opt into the `native-eval` tier (see the trust policy
   above) with the migration note recorded.

3. **Add a theorem to `SAWCoreBitvectors_proofs.lean`.** If
   the shape is general (will recur), it belongs in the
   library. Pattern-match on existing entries for style.

4. **File an issue.** If the shape is something Cryptol
   genuinely emits and the cookbook is silent, the discharge
   experience needs improvement — that's Phase 7 work.
