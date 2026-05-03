# BitVec binding: decision and rationale

*Draft — 2026-05-01.*

## TL;DR

We **keep `bitvector n := Vec n Bool`** for the foreseeable future. Lean's
native `BitVec n` is more ergonomic for downstream proofs, but the cost
of binding it correctly — proving coherence between SAWCore's
spelled-out semantics and Lean's `BitVec` operations on every edge case
— is a multi-week piece of work that hasn't paid for itself yet.

This doc records the trade-off so a future maintainer can revisit the
decision deliberately rather than re-discover it.

## What the original design said

`doc/2026-04-22_lean-backend-design.md` §5.3 called the `BitVec`
binding "the biggest Lean win" and §10 listed
`bitvector n` → `BitVec n` as a **success criterion** for the backend.
That design predates the specialization pivot and hadn't grappled with
the soundness implications.

## What's actually shipped

`CryptolToLean.SAWCoreBitvectors`:

```lean
abbrev bitvector (n : Nat) : Type :=
  CryptolToLean.SAWCoreVectors.Vec n Bool
```

i.e. an alias for `Vector Bool n`. All bitvector operations
(`bvAdd`, `bvSub`, `bvShl`, `bvSExt`, …) are declared as opaque
axioms in `CryptolToLean.SAWCorePrimitives` taking `Vec n Bool`
arguments, with their semantic meaning pinned down by SAWCore's
source rather than by reduction in Lean.

## What changes if we bind to `Lean.BitVec`

Lean's `Lean.BitVec n` is `{ toFin : Fin (2^n) }` — a packed
unsigned integer modulo `2^n`. It has native `Add`/`Sub`/`Mul`
instances that Lean simp can reduce, plus an extensive lemma
library in mathlib's `Mathlib.Data.BitVec`.

A correct binding would:

1. Provide `bitvector n := Lean.BitVec n`.
2. For each SAWCore bitvector primitive, prove `bvOp ≡ Lean.BitVec.op`
   (or its mathlib counterpart) and replace the axiom with a
   `noncomputable def` whose body is the Lean-side operation.
3. Carry the proof obligation as a `theorem` next to each
   replacement, so the equivalence is checked at Lean elaboration
   time rather than left implicit.

The downstream win is real: Cryptol bitvector specs have a body
of useful Lean lemmas to draw on (`BitVec.add_comm`,
`BitVec.shiftl_pow_two`, the whole `simp` apparatus at `BitVec`),
none of which apply to `Vec n Bool`.

## What blocks doing it now

### Semantic alignment is non-trivial on edge cases

SAWCore's bitvector operations are spelled out at the bit level in
`Prelude.sawcore` lines 1760–2116. Most of them line up with
`Lean.BitVec` directly — `bvAdd` is two's-complement addition mod
2^n on both sides — but several have edge-case semantics that
require checking:

- **`bvSDiv` / `bvSRem`**: SAW-typed at `Vec (Succ n) Bool` to
  forbid zero-width vectors; Lean's `BitVec.sdiv` is at
  `BitVec n` for any `n` and has different behaviour around
  zero divisors. Coherence here needs at minimum a case-split
  on the `Succ n` shape and a proof that `n > 0` matches the
  shape Lean expects.
- **`bvShl` / `bvShr` shift amounts**: SAW takes a `Nat` shift
  amount; Lean takes a `BitVec`. The conversion is total, but
  proving the resulting bits agree requires unfolding both
  definitions and showing that "shift by Nat n on a Vec of Bools"
  matches "BitVec.shiftLeft by BitVec.ofNat n on a packed BitVec".
- **`bvSExt` / `bvUExt` length arithmetic**: SAW's `bvSExt`
  produces `Vec (addNat m (Succ n)) Bool`; the Lean-side BitVec
  signature would need `BitVec (m + (n+1))`. Lean's `BitVec.signExtend`
  has slightly different argument shape.
- **`bvForall`**: SAW's `bvForall` quantifies over `Vec n Bool`;
  the Lean-side `BitVec` would need either to match this shape or
  to be replaced with a quantifier over `BitVec n`. Conversion
  proofs needed.

None of these are fundamental obstacles. They're each a small
proof obligation. But there are ~30 bitvector primitives, and
each needs a `theorem bvOp_eq_BitVec_op : ∀ n …, … = …` to be
sound. That's a multi-day effort even for someone fluent in both
SAWCore and `Lean.BitVec`.

### The translator's emission shape would need to change

Right now the translator emits `CryptolToLean.SAWCorePrimitives.bvAdd
n x y`. Under a `BitVec` binding, the natural emission would be
`Lean.BitVec.add x y` directly (the `n` is implicit in the BitVec
type). That's a translator change in the SpecialTreatment table —
straightforward, but every emitted `.lean.good` reference file
needs regenerating.

### mathlib dependency

Most of the `BitVec` lemma surface lives in mathlib. Importing
mathlib into `CryptolToLean` would substantially grow the
support library's transitive deps. Avoidable if we only use
core-Lean `BitVec` definitions, but that loses much of the win.

The 2026-04-22 design doc Q1 explicitly called out keeping the
support lib mathlib-free for the core path; the BitVec binding
fights that goal.

## What we lose by keeping `Vec n Bool`

User-side cost is real but bounded:

- A Lean proof about a translated Cryptol property has access only
  to the SAWCore-axiomatized operations. Reasoning about `bvAdd`
  is "by definition" (the axiom) plus whatever `unsafeAssert`
  hooks Cryptol's compile chain inserted. There's no `bvAdd_comm`
  available out of the box.
- `Lean.BitVec` and `Vec n Bool` aren't interchangeable. If a
  user wants to bridge to mathlib's lemma library, they have to
  define a coercion and prove what they need term-by-term.
- Generated output is verbose. Type signatures spell out
  `CryptolToLean.SAWCoreVectors.Vec 8 Bool` instead of
  `BitVec 8`.

For our current driving demos (rev.cry, the otherTests/saw-core-
lean coverage suite), none of these costs bite — the
`prove_print (offline_lean …)` outputs are proof stubs the user
discharges separately. Real Cryptol verification work hasn't yet
happened on top of the Lean backend.

## Decision triggers — when to revisit

Reopen this when any of the following becomes true:

1. **A user wants to discharge an `offline_lean` goal**, hits the
   "no `bvAdd_comm`-style lemmas available" wall, and the
   workaround (proving the lemma manually for `Vec n Bool`) is
   prohibitive. This is the most likely forcing function.

2. **A real Cryptol spec ports to Lean** and the translated output
   is too verbose to read. The `Vec 8 Bool` vs `BitVec 8` width
   matters more for human-readable proofs than for typechecking.

3. **mathlib's `BitVec` API stabilises** to the point where coherence
   proofs are mostly `decide` / `rfl` — at which point the
   per-primitive cost drops from "afternoon" to "minute".

4. **An external user contributes the binding**. The work is
   parallelizable across primitives; if someone wants to write the
   coherence theorems for half a dozen operations at a time, this
   is a clean external-contribution shape.

## Migration sketch (when we do it)

1. Add `Lean.BitVec` import to `CryptolToLean.SAWCoreBitvectors`.
2. Replace `abbrev bitvector` with one that pattern-matches: for
   `n = 0` we still need `Vec 0 Bool` (BitVec 0 has odd
   semantics); otherwise `BitVec n`. Actually `BitVec 0` is
   defined and inhabited (it's a unit-like type), so a flat
   `abbrev bitvector n := BitVec n` might be fine. Verify.
3. For each bv primitive, add a `theorem` proving its
   `Vec n Bool`-shaped semantic spec equals the `BitVec`-shaped
   Lean operation. Replace the axiom with `noncomputable def`.
4. Update `SpecialTreatment.hs` so the translator emits
   `Lean.BitVec.add` etc. at use sites (or keep the
   `SAWCorePrimitives.bvAdd` indirection but make it a wrapper
   over `BitVec.add`).
5. Regenerate all `.lean.good` references.
6. Test the pinned `offline_lean` goals in `test_offline_lean.saw`
   to verify they elaborate to a more useful proof shape.

Estimated cost: 1-2 weeks of focused work, dominated by the
coherence-proof obligations.

## Status

**Deferred indefinitely**. The cost is real, the trigger hasn't
fired, and the current `Vec n Bool` mapping is sound and
demonstrably works for the test suite we have. Listed as an Arc 3
item in `2026-05-01_status-and-next-steps.md`; this doc is the
"explicitly document why we're keeping `Vec n Bool`" outcome
that arc anticipated.
