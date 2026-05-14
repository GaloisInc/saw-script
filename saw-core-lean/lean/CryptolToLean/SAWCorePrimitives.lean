/-
`CryptolToLean.SAWCorePrimitives` — axiomatic + inductive stand-ins
for the SAWCore primitives that survive `scNormalize`.

The specialization approach (see `doc/2026-04-23_stage3-translator-
sketch.md`) normalizes each user term before translation. Everything
that survives is either

- a SAWCore axiom / primitive (no body), or
- a SAWCore inductive / its auto-generated recursor, or
- a SAWCore constructor,

and this file enumerates a realisation for each one the translator
emits a reference to.

**Soundness discipline.** Every realisation must be semantically
equivalent to the SAWCore source it replaces. If in doubt, prove the
equivalence. See `doc/2026-04-22_soundness.md`.

Scope: seeded for the Stage 4 implRev4 driver. Extend as further
Cryptol demos surface additional primitives.
-/

import CryptolToLean.SAWCoreVectors

namespace CryptolToLean.SAWCorePrimitives

open CryptolToLean.SAWCoreVectors (Vec)

/-! ## Inductives -/

/-- SAWCore Prelude `Either a b` — standard coproduct. Matches
Lean's standard sum but defined here so the SAWCore translator can
emit `@CryptolToLean.SAWCorePrimitives.Either.Left …` without
importing Lean's `Sum`. -/
inductive Either (α β : Type) : Type where
  | Left  : α → Either α β
  | Right : β → Either α β

/-- Cryptol Prelude `Num` (from `Cryptol.sawcore`). The marker used
throughout Cryptol's numeric-kind machinery: a finite length (via
`TCNum`) or an infinite stream marker (`TCInf`).

SAWCore's `Nat` is mapped to Lean's native `Nat` at the
'SpecialTreatment' level (with `NatPos`/`Bit0`/`Bit1`/`One`/`Zero`
collapsed to numeric literals via `UseMacro`), so `TCNum` takes a
Lean `Nat` here. If a future user term exercises SAWCore's
`Nat#rec` with a non-Lean-matching argument order we'll need to
revisit; for now specialization reduces those eliminations away
before the translator sees them. -/
inductive Num : Type where
  | TCNum : Nat → Num
  | TCInf : Num

/-! ## Nat constructor wrappers

SAWCore's `Nat` / `Pos` constructors (`Zero`, `NatPos`, `One`,
`Bit0`, `Bit1`, `Succ`) are mapped to Lean's native `Nat` via
`SpecialTreatment`. When a constructor appears fully applied to a
concrete argument the translator collapses it to a `NatLit`; when
it appears under-applied or applied to a symbolic argument it
falls through to the wrappers below. -/

@[reducible] def bit0_macro (n : Nat) : Nat := 2 * n
@[reducible] def bit1_macro (n : Nat) : Nat := 2 * n + 1

/-- SAWCore Prelude `Stream a` — infinite sequences of `a`. The
single constructor `MkStream : (Nat → a) → Stream a` packages an
indexed view of the stream. -/
inductive Stream (α : Type) : Type where
  | MkStream : (Nat → α) → Stream α

/-- SAWCore Prelude `EmptyType : sort 0` — the "end of record"
marker. Has one constructor `Empty`; Cryptol's records are encoded
as right-nested `RecordType` chains ending in `EmptyType` / `Empty`.
-/
inductive EmptyType : Type where
  | Empty : EmptyType

/-- SAWCore Prelude `RecordType` — a one-field record builder. Paired
with `RecordValue` as the single constructor. Cryptol uses nested
`RecordType` for multi-field records. -/
inductive RecordType (s : String) (α β : Type) : Type where
  | RecordValue : α → β → RecordType s α β

/-- SAWCore Prelude `UnitType` — the singleton type. SAWCore tuples
desugar to nested `PairType` chains terminating at `UnitType`. -/
inductive UnitType : Type where
  | Unit : UnitType

/-- SAWCore Prelude `PairType` — the basic product. Multi-element
SAWCore tuples are right-nested `PairType` chains terminating at
`UnitType`. -/
inductive PairType (α β : Type) : Type where
  | PairValue : α → β → PairType α β

/-! ### `Inhabited` instances for SAW-custom types

Phase 9 follow-up: tightening `error.{u}` to require `[Inhabited α]`
(matching SAW's `isort 1` semantics) means every type the
translator emits `error` at needs a Lean `Inhabited` instance.
For inductive types with a constructor that takes only Inhabited
arguments, we provide the obvious instance. -/

instance instInhabitedStream {α : Type} [Inhabited α] : Inhabited (Stream α) :=
  ⟨Stream.MkStream (fun _ => default)⟩
instance instInhabitedUnitType : Inhabited UnitType := ⟨UnitType.Unit⟩
instance instInhabitedEmptyType : Inhabited EmptyType := ⟨EmptyType.Empty⟩
instance instInhabitedPairType {α β : Type} [Inhabited α] [Inhabited β] :
    Inhabited (PairType α β) := ⟨PairType.PairValue default default⟩
instance instInhabitedRecordType {s : String} {α β : Type}
    [Inhabited α] [Inhabited β] : Inhabited (RecordType s α β) :=
  ⟨RecordType.RecordValue default default⟩

/-- `Either α β` is inhabited via the left injection when `α` is.
The right-injection variant lives below; both are needed because
the translator may select either side depending on the residual
trace. Only one is required at any given call site, so providing
both as `instance` is fine — Lean's resolution picks whichever
discharges the goal first. -/
instance instInhabitedEitherLeft {α β : Type} [Inhabited α] :
    Inhabited (Either α β) := ⟨Either.Left default⟩
instance instInhabitedEitherRight {α β : Type} [Inhabited β] :
    Inhabited (Either α β) := ⟨Either.Right default⟩

/-- Stream-endofunction inhabitedness via identity. Required for
the `(a : Type) → Stream a → Stream a` shape that appears in
Cryptol's typeclass-elaboration dead branches; identity is sound
without needing `[Inhabited a]`. -/
instance instInhabitedStreamEndo : Inhabited ((α : Type) → Stream α → Stream α) :=
  ⟨fun _ s => s⟩

/-- Projection from a SAWCore pair. Phase 8: structural def
matching SAWCore's `Pair_fst = Pair__rec α β (\\_ => α) (\\x _ => x)`.
Reducibly equal to `pairFst` further below; both names are kept
because SAWCore Prelude's `Pair_fst` is the user-facing name and
the SpecialTreatment routes to it directly. -/
def Pair_fst (α β : Type) : PairType α β → α
  | PairType.PairValue a _ => a

def Pair_snd (α β : Type) : PairType α β → β
  | PairType.PairValue _ b => b

/-! ## Opaque types (SAWCore `primitive` declarations, no body) -/

/-- SAWCore Prelude `Integer : sort 0`. Mapped to Lean's `Int` at
use sites via `SpecialTreatment`; the local def is `Int` directly
(reducible alias) so any incidental `Integer` reference reduces. -/
@[reducible] def Integer : Type := Int

/-! ## IntMod n (Phase 6 → Phase 9 follow-up)

The quotient type `Z / nZ` — Cryptol's `Z n`. SAW Prelude declares
each operation as a `primitive` (no body); we represent `IntMod n`
as `Int` (every value implicitly `mod n`) and route operations
through `Int.fmod` (floor modulus). For `n = 0`, SAW's convention
is "no reduction" (representative is the input as-is), which
matches `Int.fmod _ 0 = _`. Each function is `@[reducible]` so
SAW-named goals reduce transparently to Int arithmetic.

The signatures match `Prelude.sawcore` lines 2126-2135 exactly. -/

@[reducible] def IntMod : Nat → Type := fun _ => Int
@[reducible] def toIntMod : (n : Nat) → Int → IntMod n := fun n x => Int.fmod x n
@[reducible] def fromIntMod : (n : Nat) → IntMod n → Int := fun n x => Int.fmod x n
@[reducible] def intModEq : (n : Nat) → IntMod n → IntMod n → Bool :=
  fun n x y => decide (Int.fmod x n = Int.fmod y n)
@[reducible] def intModAdd : (n : Nat) → IntMod n → IntMod n → IntMod n :=
  fun n x y => Int.fmod (x + y) n
@[reducible] def intModSub : (n : Nat) → IntMod n → IntMod n → IntMod n :=
  fun n x y => Int.fmod (x - y) n
@[reducible] def intModMul : (n : Nat) → IntMod n → IntMod n → IntMod n :=
  fun n x y => Int.fmod (x * y) n
@[reducible] def intModNeg : (n : Nat) → IntMod n → IntMod n :=
  fun n x => Int.fmod (-x) n

/-! ## Rational (Phase 6 → Phase 9 follow-up)

SAW Prelude's `Rational` quotient type. Bound to Lean's core
`Rat` type. Operations route through Lean's `Rat` arithmetic;
`ratio a b` is `Rat.mk` (or `a / b` over `Rat`), `rationalRecip`
is reciprocal. For `b = 0`, Lean's `Rat` division returns 0
which matches SAW's convention. -/

@[reducible] def Rational : Type := Rat
@[reducible] def ratio : Int → Int → Rational := fun a b => (a : Rat) / (b : Rat)
@[reducible] def rationalEq : Rational → Rational → Bool := fun a b => decide (a = b)
@[reducible] def rationalLe : Rational → Rational → Bool := fun a b => decide (a ≤ b)
@[reducible] def rationalLt : Rational → Rational → Bool := fun a b => decide (a < b)
@[reducible] def rationalAdd : Rational → Rational → Rational := fun a b => a + b
@[reducible] def rationalSub : Rational → Rational → Rational := fun a b => a - b
@[reducible] def rationalMul : Rational → Rational → Rational := fun a b => a * b
@[reducible] def rationalNeg : Rational → Rational := fun a => -a
@[reducible] def rationalRecip : Rational → Rational := fun a => a⁻¹
@[reducible] def rationalFloor : Rational → Int := fun a => a.floor

/-! ## Floating-point (Phase 6 → Phase 9 follow-up)

SAW Prelude declares `Float` and `Double` as opaque types with
mantissa-exponent constructors and no operations. Phase 9
binds these as concrete `Int × Int` mantissa-exponent pairs —
SAW has no operations to make this binding observable, so any
inhabited concrete type is faithful. Note: SAW's `mkDouble`
declaration in `Prelude.sawcore:2163` returns `Float` (not
`Double`) — possibly a SAW typo, but our def matches exactly
per the soundness-paramount rule (no silent corrections). If
SAW fixes the upstream declaration, this should be updated. -/

@[reducible] def Float : Type := Int × Int
@[reducible] def mkFloat : Int → Int → Float := fun m e => (m, e)
@[reducible] def Double : Type := Int × Int
-- N.B.: SAW's mkDouble returns Float, not Double — see
-- `saw-core/prelude/Prelude.sawcore:2163`. Faithful binding.
@[reducible] def mkDouble : Int → Int → Float := fun m e => (m, e)

/-! ## Arithmetic primitives

These are declared as reducible wrappers over Lean's native
arithmetic rather than opaque axioms. Definitional equality of
arithmetic is needed for type-checking vector sizes (e.g.
Cryptol's `[0..10]` has length `addNat 1 (subNat 10 0)` which Lean
must recognise as `11` to match a `Vec 11` annotation).

SAWCore's `subNat` saturates at zero (`subNat n m = max 0 (n - m)`);
Lean's `Nat.sub` has the same truncated-subtraction semantics. -/

@[reducible] def addNat : Nat → Nat → Nat := Nat.add
@[reducible] def subNat : Nat → Nat → Nat := Nat.sub
@[reducible] def minNat : Nat → Nat → Nat := Nat.min
@[reducible] def maxNat : Nat → Nat → Nat := Nat.max
@[reducible] def mulNat : Nat → Nat → Nat := Nat.mul
@[reducible] def expNat : Nat → Nat → Nat := fun m n => Nat.pow m n
@[reducible] def doubleNat : Nat → Nat := fun n => 2 * n
@[reducible] def pred     : Nat → Nat := Nat.pred
/-- SAW Prelude `divNat x y = (divModNat x y).0`. Matches Lean's
`Nat.div`, which has the same "divide by zero gives zero" convention
SAW inherits from `divModNat`. -/
@[reducible] def divNat : Nat → Nat → Nat := Nat.div
/-- SAW Prelude `modNat x y = (divModNat x y).1`. Matches Lean's
`Nat.mod`. -/
@[reducible] def modNat : Nat → Nat → Nat := Nat.mod
/-- SAW Prelude primitive `divModNat : Nat -> Nat -> Nat * Nat`.
Returns (quotient, remainder). -/
@[reducible] def divModNat : Nat → Nat → Nat × Nat :=
  fun x y => (Nat.div x y, Nat.mod x y)

/-- SAWCore `widthNat n` — the number of bits to represent `n`.
`widthNat 0 = 0`, `widthNat 1 = 1`, `widthNat 2 = widthNat 3 = 2`,
... matches Lean's `Nat.log2 n + 1` for n > 0, with 0 special-cased
to 0 (Lean's `Nat.log2 0 = 0` would give 1 without the guard). -/
@[reducible] def widthNat : Nat → Nat := fun n =>
  if n = 0 then 0 else Nat.log2 n + 1

-- Comparison wrappers — reducible aliases over Lean's native Nat
-- comparisons. These are only sound because we've already
-- committed to SAW Nat ≡ Lean Nat at the value level.
@[reducible] def equalNat : Nat → Nat → Bool := fun a b => decide (a = b)
@[reducible] def ltNat    : Nat → Nat → Bool := fun a b => decide (a < b)
@[reducible] def leNat    : Nat → Nat → Bool := fun a b => decide (a ≤ b)

/-! ### Integer ops (Phase 9 follow-up: defined via Lean's `Int`)

SAW's concrete simulator (`SAWCore.Simulator.Concrete`) defines
`bpIntDiv = Haskell div` and `bpIntMod = Haskell mod`, which are
**floor** division/modulus (non-negative remainder for positive
divisor). This corresponds to Lean's `Int.fdiv` / `Int.fmod`,
NOT `Int.div` / `Int.mod` (which are truncated). -/
@[reducible] def intAdd : Int → Int → Int := fun a b => a + b
@[reducible] def intSub : Int → Int → Int := fun a b => a - b
@[reducible] def intMul : Int → Int → Int := fun a b => a * b
@[reducible] def intDiv : Int → Int → Int := Int.fdiv
@[reducible] def intMod : Int → Int → Int := Int.fmod
@[reducible] def intNeg : Int → Int := fun a => -a
@[reducible] def intEq  : Int → Int → Bool := fun a b => decide (a = b)
@[reducible] def intLe  : Int → Int → Bool := fun a b => decide (a ≤ b)
@[reducible] def intLt  : Int → Int → Bool := fun a b => decide (a < b)
@[reducible] def natToInt : Nat → Int := Int.ofNat
@[reducible] def intToNat : Int → Nat := Int.toNat

/-! ## Vec ↔ BitVec converters (Phase 9 / native BitVec binding)

SAW models bitvectors as `Vec n Bool` (`bitvector n := Vec n
Bool`) MSB-first: position 0 of the Vec is the most-significant
bit. Lean's `BitVec n` is a packed `Fin (2^n)`. These converters
let us route SAW's bv ops through Lean's native `BitVec` machinery
while keeping the surface representation `Vec n Bool` (so the
translator's emission shape, the user-facing types in goals, and
all existing `.lean.good` files stay unchanged). -/

/-- `Vec n Bool` (MSB-first) → `BitVec n`. Folds left, accumulating
the integer value MSB-first, then packs via `BitVec.ofNat`. -/
def vecToBitVec {n : Nat} (v : Vec n Bool) : BitVec n :=
  BitVec.ofNat n (v.foldl (fun acc b => 2 * acc + b.toNat) 0)

/-- `BitVec n` → `Vec n Bool` (MSB-first). Reads bits MSB-first
via `getMsbD`. -/
def bitVecToVec {n : Nat} (bv : BitVec n) : Vec n Bool :=
  Vector.ofFn (fun (i : Fin n) => bv.getMsbD i.val)

/-! ### Vec ↔ BitVec round-trip coherence

These two axioms assert that `vecToBitVec` and `bitVecToVec` are
mutually inverse — i.e., that our two representations of an
n-bit value (`Vec n Bool` MSB-first and `Lean.BitVec n`) carry
the same information. They are decidable for any concrete `n`
(use `decide`), so each axiom can be machine-checked at any
finite width; the general statement just needs an induction on
`n` that we haven't worked through.

This is the **only** soundness commitment of Phase 9. Replacing
~30 opaque `bvAdd_*` / `bvXor_*` / `bvSub_*` / `bvEq_*` axioms
with 2 coherence axioms is a strict trust-posture improvement:
under these two axioms, every bv arithmetic / bitwise / comparison
property becomes a theorem provable from Lean's `BitVec` lemma
library. (See `SAWCoreBitvectors_proofs.lean`.)

If a future audit invalidates the converters, exactly these
axioms break — and the entire downstream library breaks loudly,
not silently. -/

/-- Round-trip: `BitVec → Vec → BitVec` is the identity. -/
axiom vecToBitVec_bitVecToVec {n : Nat} (bv : BitVec n) :
    vecToBitVec (bitVecToVec bv) = bv

/-- Round-trip: `Vec → BitVec → Vec` is the identity. -/
axiom bitVecToVec_vecToBitVec {n : Nat} (v : Vec n Bool) :
    bitVecToVec (vecToBitVec v) = v

/-! ## Bitvector primitives

Phase 9: converted from opaque axioms to `noncomputable def`s
backed by `Lean.BitVec`. Keeping `Vec n Bool` as the surface type
means the translator emission, existing `.lean.good` files, and
proof-side users never see `BitVec` unless they want to —
`vecToBitVec` is the exposed bridge. The defining equations let
`decide` close concrete-value goals (e.g. `bvAdd 8 (bvNat 8 5)
(bvNat 8 3) = bvNat 8 8`) and let mathlib `BitVec` lemmas reach
SAW-named ops via the `_eq_BitVec_*` theorems in
`SAWCoreBitvectors_proofs.lean`.

A few ops stay axiomatic because their SAW-vs-Lean coherence is
non-trivial enough to defer to a focused follow-up:

  - `bvSDiv` / `bvSRem`: SAW types these at `Vec (Succ n) Bool` to
    forbid zero-width vectors; Lean's `BitVec.sdiv` / `BitVec.smod`
    work at any `n`. Coherence around zero divisors needs a
    case-split. Stays axiomatic.
  - `bvSExt`: SAW's `bvSExt m n : Vec (n+1) Bool → Vec (m + (n+1))
    Bool` has a length shape Lean's `BitVec.signExtend` doesn't
    quite match. Coherence needs the length arithmetic worked
    through. Stays axiomatic.
  - `bvPopcount` / `bvCountLeadingZeros` / `bvCountTrailingZeros` /
    `bvLg2`: Lean has `BitVec.toNat`-based equivalents but the
    coherence is bit-level rather than int-level. Deferred.

The non-primitive bv ops (`bvNot`, `bvAnd`, `bvOr`, `bvXor`,
`bvEq`) are SAWCore Prelude /defs/ rather than primitives — their
bodies use `map` / `bvZipWith` / `vecEq` over individual `Bool`
ops. We keep them opaque via `leanOpaqueBuiltins` (in
`SAWCentral.Prover.Exporter`) so normalization doesn't expose the
inner machinery, then provide top-level defs here that route
through `BitVec`. -/

noncomputable def bvNat (n : Nat) (k : Nat) : Vec n Bool :=
  bitVecToVec (BitVec.ofNat n k)
noncomputable def bvToNat (n : Nat) (v : Vec n Bool) : Nat :=
  (vecToBitVec v).toNat
noncomputable def bvToInt (n : Nat) (v : Vec n Bool) : Int :=
  (vecToBitVec v).toInt
noncomputable def intToBv (n : Nat) (k : Int) : Vec n Bool :=
  bitVecToVec (BitVec.ofInt n k)
noncomputable def sbvToInt (n : Nat) (v : Vec n Bool) : Int :=
  (vecToBitVec v).toInt

noncomputable def bvAdd (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) + (vecToBitVec y))
noncomputable def bvSub (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) - (vecToBitVec y))
noncomputable def bvMul (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) * (vecToBitVec y))
noncomputable def bvNeg (n : Nat) (x : Vec n Bool) : Vec n Bool :=
  bitVecToVec (- (vecToBitVec x))
noncomputable def bvUDiv (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x).udiv (vecToBitVec y))
noncomputable def bvURem (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x).umod (vecToBitVec y))

noncomputable def bvSDiv (n : Nat) (x y : Vec (n + 1) Bool) : Vec (n + 1) Bool :=
  bitVecToVec ((vecToBitVec x).sdiv (vecToBitVec y))
noncomputable def bvSRem (n : Nat) (x y : Vec (n + 1) Bool) : Vec (n + 1) Bool :=
  bitVecToVec ((vecToBitVec x).srem (vecToBitVec y))

noncomputable def bvShl (w : Nat) (x : Vec w Bool) (i : Nat) : Vec w Bool :=
  bitVecToVec ((vecToBitVec x) <<< i)
noncomputable def bvShr (w : Nat) (x : Vec w Bool) (i : Nat) : Vec w Bool :=
  bitVecToVec ((vecToBitVec x) >>> i)

noncomputable def bvSShr (w : Nat) (x : Vec (w + 1) Bool) (i : Nat) : Vec (w + 1) Bool :=
  bitVecToVec ((vecToBitVec x).sshiftRight i)

noncomputable def bvNot (n : Nat) (x : Vec n Bool) : Vec n Bool :=
  bitVecToVec (~~~ (vecToBitVec x))
noncomputable def bvAnd (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) &&& (vecToBitVec y))
noncomputable def bvOr  (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) ||| (vecToBitVec y))
noncomputable def bvXor (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) ^^^ (vecToBitVec y))

noncomputable def bvEq  (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x) == (vecToBitVec y)
noncomputable def bvult (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x).ult (vecToBitVec y)
noncomputable def bvule (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x).ule (vecToBitVec y)
noncomputable def bvugt (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec y).ult (vecToBitVec x)
noncomputable def bvuge (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec y).ule (vecToBitVec x)
noncomputable def bvslt (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x).slt (vecToBitVec y)
noncomputable def bvsle (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x).sle (vecToBitVec y)
noncomputable def bvsgt (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec y).slt (vecToBitVec x)
noncomputable def bvsge (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec y).sle (vecToBitVec x)

noncomputable def bvUExt (m n : Nat) (v : Vec n Bool) : Vec (m + n) Bool :=
  bitVecToVec ((vecToBitVec v).zeroExtend (m + n))

noncomputable def bvSExt (m n : Nat) (v : Vec (n + 1) Bool) : Vec (m + (n + 1)) Bool :=
  bitVecToVec ((vecToBitVec v).signExtend (m + (n + 1)))

/-! ### Population count, leading/trailing zeros, log2

Bit-level Nat-counting operations. Each is defined by folding
over `Vec n Bool` with a `(count, locked)` state pair so that
counting stops at the first relevant transition (clz: first
`true` from MSB; ctz: first `true` from LSB). Result encoded
as `bvNat n k`. -/

/-- Population count: number of `true` bits, encoded as a bv. -/
noncomputable def bvPopcount (n : Nat) (v : Vec n Bool) : Vec n Bool :=
  bvNat n (v.foldr (fun b acc => acc + b.toNat) 0)

/-- Number of leading-zero bits (counting from MSB-first position
0). For all-zero input returns `n`. The state pair `(count,
locked)` becomes locked once we see any `true` bit, so subsequent
zeros don't increment `count`. -/
noncomputable def bvCountLeadingZeros (n : Nat) (v : Vec n Bool) : Vec n Bool :=
  bvNat n (v.foldl (fun (acc : Nat × Bool) b =>
    if acc.2 then acc
    else if b then (acc.1, true)
    else (acc.1 + 1, false)) (0, false)).1

/-- Number of trailing-zero bits (counting from LSB, position
`n-1` MSB-first). For all-zero input returns `n`. Symmetric to
clz but folds from the right (LSB-first traversal). -/
noncomputable def bvCountTrailingZeros (n : Nat) (v : Vec n Bool) : Vec n Bool :=
  bvNat n (v.foldr (fun b (acc : Nat × Bool) =>
    if acc.2 then acc
    else if b then (acc.1, true)
    else (acc.1 + 1, false)) (0, false)).1

/-- Floor of log base 2 of the bv (interpreted as Nat). For
input 0, returns 0 by SAW convention (matches `Nat.log2 0 = 0`). -/
noncomputable def bvLg2 (n : Nat) (v : Vec n Bool) : Vec n Bool :=
  bvNat n (Nat.log2 (vecToBitVec v).toNat)

/-! ## Vector primitives

Phase 8 (2026-05-02 evening): converted from axioms to structural
defs. `gen` / `atWithDefault` / `foldr` / `foldl` / `shiftL` /
`shiftR` use Lean's stdlib `Vector` operations underneath, so
the resulting goals reduce in proofs without needing axiom-firing.
`rotateL`/`rotateR` stay axiomatic for now (modular indexing
needs a small structural realisation; deferred to a follow-up). -/

/-- SAWCore `gen n a f = [f 0, f 1, …, f (n-1)]`. Defined via
`Vector.ofFn` over `Fin n` indices; `f`'s `Nat → α` signature is
bridged by projecting `Fin.val`. -/
def gen (n : Nat) (α : Type) (f : Nat → α) : Vec n α :=
  Vector.ofFn (fun (i : Fin n) => f i.val)

/-- SAWCore `shiftL n α z v i` — shift @v@ left by @i@ positions,
filling with @z@ on the right. Generic over the element type; the
bitvector shift `bvShl` is the @α = Bool@ specialization. -/
def shiftL (n : Nat) (α : Type) (z : α) (v : Vec n α) (i : Nat) : Vec n α :=
  Vector.ofFn (fun (j : Fin n) =>
    if h : j.val + i < n then v[j.val + i] else z)

/-- SAWCore `shiftR n α z v i` — shift right, filling with @z@. -/
def shiftR (n : Nat) (α : Type) (z : α) (v : Vec n α) (i : Nat) : Vec n α :=
  Vector.ofFn (fun (j : Fin n) =>
    if h : j.val ≥ i then
      if h2 : j.val - i < n then v[j.val - i] else z
    else z)

/-- SAWCore `rotateL n α v i` — rotate @v@ left by @i@ positions.
The Cryptol `<<<` operator lowers here. Generic over the element
type. Defined via modular indexing: `result[j] = v[(j + i) mod n]`. -/
def rotateL (n : Nat) (α : Type) (v : Vec n α) (i : Nat) : Vec n α :=
  Vector.ofFn (fun (j : Fin n) =>
    have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have h : (j.val + i) % n < n := Nat.mod_lt _ hpos
    v[(j.val + i) % n])

/-- SAWCore `rotateR n α v i` — rotate @v@ right by @i@ positions.
The Cryptol `>>>` operator lowers here. Defined via modular
indexing: `result[j] = v[(j + (n - i mod n)) mod n]` (rotate right
by i = rotate left by n - i mod n). -/
def rotateR (n : Nat) (α : Type) (v : Vec n α) (i : Nat) : Vec n α :=
  Vector.ofFn (fun (j : Fin n) =>
    have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have h : (j.val + (n - i % n)) % n < n := Nat.mod_lt _ hpos
    v[(j.val + (n - i % n)) % n])

/-- SAWCore `atWithDefault n a d v i` is `v[i]` if `i < n`, else `d`.
Defined via dependent if + `Vector` indexing; the `Vector α n` index
operation requires a proof `i < n`, supplied by the if-discriminator. -/
def atWithDefault (n : Nat) (α : Type) (d : α) (v : Vec n α) (i : Nat) : α :=
  if h : i < n then v[i] else d

/-- SAWCore `foldr a b n f z v = f v[0] (f v[1] (... (f v[n-1] z))).
Right-associative; matches Lean's `Vector.foldr` modulo arg-order. -/
def foldr (α β : Type) (n : Nat) (f : α → β → β) (z : β) (v : Vec n α) : β :=
  Vector.foldr f z v

/-- SAWCore `foldl a b n f z v = f (... (f (f z v[0]) v[1])) v[n-1]`.
Matches Lean's `Vector.foldl`. -/
def foldl (α β : Type) (n : Nat) (f : β → α → β) (z : β) (v : Vec n α) : β :=
  Vector.foldl f z v

/-! ## Phase β: Except-wrapped variants of polymorphic helpers

Phase β translates every SAW value-domain expression to a Lean term
at type `Except String τ`. The polymorphic helpers above have
unwrapped Lean signatures and are unusable directly from Phase β
output (the function arg / vector arg / default arg arrive
Except-wrapped, the bare helper expects raw). These wrapped
counterparts accept and return the right Except types, short-
circuiting on `Except.error` per Cryptol's error semantics: if any
element-producing computation errors, the aggregate operation
errors with the first encountered message.

The translator routes SAW's helper names to these wrapped variants
via `UseMacro` mappings (not `mapsTo`) so the generic call-site
lift in 'SAWCoreLean.Term.applied' doesn't insert a redundant
`Pure.pure` around the already-wrapped result.

Soundness: each wrapped variant is semantically the lift of the raw
helper into the Except monad — applied to fully `Except.ok`-wrapped
inputs, they produce an `Except.ok`-wrapped output equal (by the
helper's own definition) to the raw helper on the unwrapped
arguments. -/

/-- Wrapped variant of 'gen'. The element-producing function arg
returns wrapped elements; the result is a wrapped vector. Short-
circuits on the first `Except.error` element. -/
def genM (n : Nat) (α : Type) (f : Nat → Except String α) :
    Except String (Vec n α) :=
  Vector.ofFnM (fun (i : Fin n) => f i.val)

/-- Wrapped variant of 'atWithDefault'. The default and vector
arrive wrapped; the Nat index stays raw (Nat is type-level and
doesn't wrap under Phase β). -/
def atWithDefaultM (n : Nat) (α : Type)
    (d : Except String α) (v : Except String (Vec n α)) (i : Nat) :
    Except String α := do
  let vec ← v
  if _h : i < n then pure vec[i] else d

/-- Wrapped variant of 'foldr'. The folding function takes wrapped
α and accumulator, returns wrapped accumulator. The pre-existing
'foldr' raw definition stays for any non-monadic call paths. -/
def foldrM (α β : Type) (n : Nat)
    (f : Except String α → Except String β → Except String β)
    (z : Except String β) (v : Except String (Vec n α)) :
    Except String β :=
  Bind.bind v (fun vec =>
    Vector.foldr (fun a acc => f (pure a) acc) z vec)

/-- Wrapped variant of 'foldl'. Symmetric to 'foldrM'. -/
def foldlM (α β : Type) (n : Nat)
    (f : Except String β → Except String α → Except String β)
    (z : Except String β) (v : Except String (Vec n α)) :
    Except String β :=
  Bind.bind v (fun vec =>
    Vector.foldl (fun acc a => f acc (pure a)) z vec)

/-- Lift a Vec of wrapped elements into a wrapped Vec, propagating
the first 'Except.error' encountered. Phase β emits SAW array
literals as @#v[Pure.pure e₀, Pure.pure e₁, …]@ — a Vec whose
elements are individually Except-wrapped; the surrounding context
expects @Except String (Vec n α)@. 'vecSequenceM' bridges the gap
by sequencing the inner Except through the monad. -/
def vecSequenceM (n : Nat) (α : Type) (v : Vec n (Except String α)) :
    Except String (Vec n α) :=
  Vector.mapM id v

/-- SAWCore `zip a b m n v w = [(v[0], w[0]), …, (v[k-1], w[k-1])]`
where `k = min m n`. The result type uses SAWCore's @#(a, b)@
syntax which the SAW typechecker expands to right-nested-with-Unit:
`PairType a (PairType b UnitType)` (per `Typechecker.hs:414-418`).
Phase 9 follow-up: was axiomatic; now defined via `Vector.ofFn`
and length-bound proofs from `Nat.min_le_left/right`. -/
def zip (α β : Type) (m n : Nat) (v : Vec m α) (w : Vec n β) :
    Vec (minNat m n) (PairType α (PairType β UnitType)) :=
  Vector.ofFn (fun (i : Fin (Nat.min m n)) =>
    have hm : i.val < m := Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left m n)
    have hn : i.val < n := Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right m n)
    PairType.PairValue (v.get ⟨i.val, hm⟩)
      (PairType.PairValue (w.get ⟨i.val, hn⟩) UnitType.Unit))

/-! ## Stream destructor

A reducible accessor for `Stream`'s index function. The translator
emits this in lowered fix terms (see `mkStreamFix` below) to project
the index function out of a `Stream` value produced by the body.
Reducible so iota-reduction fires through it without a `simp` call. -/

@[reducible] def streamIdx (α : Type) : Stream α → Nat → α
  | Stream.MkStream f, i => f i

/-! ## Recursion lowering helpers

Translator targets for `Prelude.fix` shapes recognized by
`SAWCoreLean.FixShapes` (Phase 5). These helpers are *not* SAWCore
primitives — they're Lean-side total definitions that play the role
of `fix` in shapes where Cryptol's productivity guarantee makes the
fix denote a uniquely-determined value.

Soundness assumption (documented in
`doc/2026-05-02_recursion-design.md` §"Soundness argument"): every
`fix` matched by the FixShapes recognizer is *productive* — Cryptol's
type checker enforces this at the source level, and `scNormalizeForLean`
preserves it. Under that assumption, each helper computes the unique
fixed point. Productivity itself is residual trust inherited from
Cryptol; we don't introduce it. -/

/-- Structurally builds the prefix `[v 0, v 1, …, v (k-1)]` of a
stream defined by productive corecursion. Each `v i` is computed by
`body lookup_i i` where `lookup_i j` is `v j` for `j < i` and the
supplied default `d` for `j ≥ i`. -/
def mkStreamFixPrefix (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) : Nat → List α
  | 0     => []
  | k + 1 =>
      let prev := mkStreamFixPrefix α d body k
      prev ++ [body (fun j => prev.getD j d) k]

/-- Index function for a stream defined by productive corecursion.
Returns the i-th element by building the prefix `[v 0, …, v i]` and
reading the last entry. -/
def mkStreamFixIdx (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) (i : Nat) : α :=
  (mkStreamFixPrefix α d body (i + 1)).getD i d

/-- SAWCore translator target for
`fix (Stream α) (\rec ⇒ MkStream α (\i ⇒ body[rec, i]))` after the
recognizer rewrites every `Stream#rec α (\_ ⇒ α) (\s ⇒ s J) rec`
in `body` to `lookup J`. The result is the unique productive fixed
point. -/
def mkStreamFix (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) : Stream α :=
  Stream.MkStream (mkStreamFixIdx α d body)

/-! ## Bounded Vec fold helper

For SAWCore `fix (Vec n α) (\rec ⇒ gen n α (\i ⇒ body[rec, i]))` —
the popcount-style bounded recursive Vec construction. Builds the
n-element prefix structurally on the index, then wraps with
`Vector.ofFn` to land in `Vec n α`.

Soundness: the productivity assumption (Cryptol enforces well-
foundedness on the body's accesses to `rec`) makes the LFP
unique and equal to this bottom-up build. -/

def genFixListBuild (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) : Nat → List α
  | 0     => []
  | k + 1 =>
      let prev := genFixListBuild α d body k
      prev ++ [body (fun j => prev.getD j d) k]

def genFixIdx (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) (i : Nat) : α :=
  (genFixListBuild α d body (i + 1)).getD i d

/-- SAWCore translator target for
`fix (Vec n α) (\rec ⇒ gen n α (\i ⇒ body[rec, i]))` after the
recognizer rewrites `rec` accesses to `lookup`-form. Returns the
unique productive fixed point, structurally built. -/
def genFix (n : Nat) (α : Type) (d : α)
    (body : (Nat → α) → Nat → α) : Vec n α :=
  Vector.ofFn (fun (i : Fin n) => genFixIdx α d body i.val)

/-! ## Pair projections (reducible, for Phase 5 lowering)

The translator-emitted lowering for `fix (PairType1 (Stream α) (Stream β)) ...`
projects the two streams out of the body's PairType result via
these helpers. Reducible so iota-reduction fires in proofs over
the lowered output without having to call `simp`. -/

@[reducible] def pairFst (α β : Type) : PairType α β → α
  | PairType.PairValue a _ => a

@[reducible] def pairSnd (α β : Type) : PairType α β → β
  | PairType.PairValue _ b => b

/-! ## Mutual stream corecursion helper

For SAWCore `fix (PairType1 (Stream α) (Stream β)) (\x ⇒ PairValue1
_ _ (MkStream α f₁) (MkStream β f₂))` where `f₁`/`f₂` access the
recursive `x` via `Stream#rec` over `PairType1#rec1` projections.
Builds the two streams' prefixes simultaneously by structural
recursion on the index. The translator-emitted body functions
(`bodyα` / `bodyβ`) take both lookup functions plus the current
index and return the next element for each stream. -/

def mkStreamFixPairPrefix (α β : Type) (dα : α) (dβ : β)
    (bodyα : (Nat → α) → (Nat → β) → Nat → α)
    (bodyβ : (Nat → α) → (Nat → β) → Nat → β) :
    Nat → List α × List β
  | 0     => ([], [])
  | k + 1 =>
      let prev := mkStreamFixPairPrefix α β dα dβ bodyα bodyβ k
      let lkα := fun j => prev.1.getD j dα
      let lkβ := fun j => prev.2.getD j dβ
      (prev.1 ++ [bodyα lkα lkβ k], prev.2 ++ [bodyβ lkα lkβ k])

def mkStreamFixPairIdxA (α β : Type) (dα : α) (dβ : β)
    (bodyα : (Nat → α) → (Nat → β) → Nat → α)
    (bodyβ : (Nat → α) → (Nat → β) → Nat → β) (i : Nat) : α :=
  ((mkStreamFixPairPrefix α β dα dβ bodyα bodyβ (i + 1)).1).getD i dα

def mkStreamFixPairIdxB (α β : Type) (dα : α) (dβ : β)
    (bodyα : (Nat → α) → (Nat → β) → Nat → α)
    (bodyβ : (Nat → α) → (Nat → β) → Nat → β) (i : Nat) : β :=
  ((mkStreamFixPairPrefix α β dα dβ bodyα bodyβ (i + 1)).2).getD i dβ

/-- SAWCore translator target for `fix (PairType1 (Stream α) (Stream β)) body`
after recognizer extraction. Returns the productive fixed point as a
`PairType (Stream α) (Stream β)` mirroring SAWCore's `PairValue1`. -/
def mkStreamFixPair (α β : Type) (dα : α) (dβ : β)
    (bodyα : (Nat → α) → (Nat → β) → Nat → α)
    (bodyβ : (Nat → α) → (Nat → β) → Nat → β) :
    PairType (Stream α) (Stream β) :=
  PairType.PairValue
    (Stream.MkStream (mkStreamFixPairIdxA α β dα dβ bodyα bodyβ))
    (Stream.MkStream (mkStreamFixPairIdxB α β dα dβ bodyα bodyβ))

/-! ## Unsafe / transport primitives -/

/-- SAWCore's `coerce` transports a value across a type equality.
Phase 9 follow-up: this is just Lean's `cast`, not a soundness
gap — `Eq Type α β` is a real proof that types are equal, and
type-equality transport is admissible (it's literally an
identity function modulo the type label). The unsoundness
attached to coerce in practice comes from chaining it with
`unsafeAssert` to fabricate the required `Eq Type α β`; this
def doesn't introduce any new attack vector beyond what
`unsafeAssert` already provides. -/
@[reducible] def coerce : (α β : Type) → @Eq Type α β → α → β :=
  fun _ _ h x => cast h x

/-! ### `unsafeAssert` — discharged as a proof obligation

SAW declares `axiom unsafeAssert : (a : sort 1) → (x y : a) →
Eq a x y` (Prelude.sawcore:212) — an assertion-without-proof
that SAW falls back to when its normalizer can't reduce a
type-level @Nat@ equality (e.g. @addNat (subNat 16 8) 8 = 16@ in
a @Vec@ size).

SAW does *not* come with a proof. Transcribing as a Lean axiom
would import SAW's unsoundness; transcribing as a `def` returning
a fabricated proof would be the same mistake.

The principled approach (mirrors Rocq's `solveUnsafeAssert`): SAW's
`unsafeAssert α x y` translates to an **explicit proof obligation**
@Eq α x y@ at the call site, with a Lean tactic
@saw_unsafeAssert@ that *attempts the discharge* using only sound
tactics. When the tactic succeeds, the resulting proof term is a
genuine proof of the equality. When it fails, elaboration errors
loud and the user must either:

* close the obligation manually with a real proof, or
* refactor the SAW workflow so it doesn't emit the assertion in
  the first place.

We never trust SAW's claim — the discharge always has to prove
it. -/

/-- Lemma library that `saw_unsafeAssert` rewrites with.
The corresponding Rocq theorems (in
`CryptolPrimitivesForSAWCoreExtra.v`) are `Eq_TCNum`, `min_nn`,
`min_nSn`, `min_Snn`. -/

theorem Num_TCNum_inj (a b : Nat) (h : a = b) : Num.TCNum a = Num.TCNum b :=
  h ▸ rfl

theorem Nat_min_self (n : Nat) : min n n = n := Nat.min_self n
theorem Nat_min_succ_right (n : Nat) : min n (n+1) = n :=
  Nat.min_eq_left (Nat.le_succ n)
theorem Nat_min_succ_left  (n : Nat) : min (n+1) n = n :=
  Nat.min_eq_right (Nat.le_succ n)

/-- The `saw_unsafeAssert` tactic: discharge a SAW-emitted size-
coercion proof obligation. Tries (in order):

* `rfl` — cheapest case; closes when both sides are
  definitionally equal (e.g. SAW emitted @unsafeAssert α x x@).
* `decide` — concrete decidable equalities (e.g.
  @Num.TCNum 16 = Num.TCNum 16@ with concrete Nats).
* `omega` — symbolic Nat arithmetic equalities (e.g.
  @addNat (subNat 16 8) 8 = 16@ where SAW didn't reduce).
* `simp` with the `Num`/`Nat` rewrite lemmas — pushes through
  the SAW-specific wrappers, then retries `rfl`/`omega`.

All tactics used are sound: if any of them closes the goal, the
resulting proof term is genuine. If the goal is symbolic in a way
none of them can close, elaboration fails loud with the open
obligation visible to the user. -/
syntax "saw_unsafeAssert" : tactic
macro_rules
  | `(tactic| saw_unsafeAssert) =>
    `(tactic| first
       | rfl
       | decide
       | (simp only [Num_TCNum_inj, Nat_min_self, Nat_min_succ_left,
                     Nat_min_succ_right]; first | rfl | omega | decide)
       | omega)

/-! ### `error` / `error_unrestricted` — DELETED, NOT TRANSLATED

SAW declares `primitive error : (a : isort 1) → String → a`. The
old two-tier design transcribed this as
`axiom error_unrestricted.{u} : (α : Sort (u+1)) → String → α`,
which is *unsound*: from `error_unrestricted Empty "" : Empty`
one can derive `False`. Every Lean proof that depends on this
axiom is meaningless under standard semantics.

The principled model: Cryptol's semantic domain is "value or
error", not "value". A Cryptol expression of type `α` should
translate as `Option α` (or `Except String α` if we want to
preserve messages), and `error msg` becomes `Option.none`. No
axiom needed; soundness preserved.

That refactor (Cryptol monadic emission) is planned but not
yet implemented. Until it lands:

* The `error_unrestricted` axiom is removed.
* The `error.{u}` user-facing `def` is also removed (Lean
  discharges that need a partial-value model should use
  `Option`/`Except` directly).
* `SpecialTreatment` maps SAW's `Prelude.error` to @reject@;
  SAW-emitted error paths fail loud at translation time.

Refactor a Cryptol workflow that depends on error paths
*before* trying to discharge it in Lean. -/

/-! ## Two error mechanisms — different semantic intents

The translator emits TWO distinct error helpers, intentionally:

* 'saw_throw_error' — for SAWCore's user-facing 'Prelude.error'
  keyword. Returns @Except String α@. Errors PROPAGATE visibly
  through subsequent 'Bind.bind' chains, matching Cryptol's
  semantics that 'error "msg"' is a real failure mode users
  should be able to reason about.

* 'saw_unreachable_default' — for fix-shape lowerings' lookup-
  out-of-bounds positions. Returns raw @α@ via 'Inhabited.default'.
  The position is GUARANTEED UNREACHABLE by Cryptol's productivity
  check; the default exists only because Lean's type system
  demands a typed value at the position. If reached (which would
  be a Cryptol typechecker bug), the function silently uses the
  inhabited default rather than propagating an error — that
  matches the semantic intent ("unreachable").

These are NOT interchangeable. Using 'Except.error' at fix-shape
default positions would cause every fix-built stream to surface
as 'Except.error' (since 'mkStreamFix' would have to handle the
wrapped default), which is wrong — Cryptol promises the default
isn't reached, and we should reflect that. Using 'Inhabited.default'
for 'Prelude.error' would silently mask user-visible errors,
also wrong.

Both helpers are Level-1 sound (no path to 'False'). They differ
in Level-2 commitment: 'saw_throw_error' preserves errors faithfully,
'saw_unreachable_default' has residual trust on Cryptol's
productivity. -/

/-- Wrapped 'Except.error' for SAWCore `error α msg` translation:
the message argument arrives wrapped (Phase β wraps any
SAWCore-value expression, including the @appendString …@ chain
that Cryptol uses to build error strings). Bind the message to
get a raw 'String', then construct the error. -/
@[reducible] def saw_throw_error (α : Type)
    (msg : Except String String) : Except String α :=
  Bind.bind msg Except.error

/-! ### `saw_unreachable_default` — typed dummy for fix-shape lowerings

The translator lowers @Prelude.fix@ over @Vec n α@ / @Stream α@ to
direct calls to 'mkStreamFix' / 'genFix' / 'mkStreamFixPair'. Each
requires a "lookup out of bounds" default at type α — a position
that Cryptol's productivity check guarantees is unreachable.
Previously the translator emitted @error_unrestricted α "msg"@,
but that axiom was deleted in Phase α (it was unsound).

This helper provides a typed default at any 'Inhabited' type. The
@msg@ is preserved for diagnostics if the user ever inspects the
emitted term; semantically it's @Inhabited.default@, which is
'noncomputable'-safe and produces a real Lean value.

**Residual trust**: if Cryptol's productivity check is wrong AND
the position is in fact reached at evaluation, this returns a
specific value (the inhabited default) rather than an error.
That matches the existing residual-trust position around fix
lowerings — Cryptol's well-foundedness is the gate; if it lies,
the lowering's correctness is forfeit regardless. Documented in
@doc/residual-trust.md@. -/
@[reducible] def saw_unreachable_default (α : Type) [Inhabited α]
    (_msg : String) : α :=
  default

/-! ## SAW-Prelude string operations

SAW's `appendString`, `equalString`, and `bytesToString` come up
in real workflows because Cryptol's `error "msg"` desugars (via
`Cryptol.ecError`) to
`error α (appendString "encountered call to ..." (bytesToString len bytes))`
— so any Cryptol code that mentions `error "msg"` surfaces these
primitives after Cryptol→SAWCore elaboration. The `error` itself
routes to `error_unrestricted` (above), but its String argument
is built via these ops.

Audit (CG-4, 2026-05-07): pre-mapping these primitives were
catalogued as `reject` SpecialTreatments — any Cryptol module
using `error` would refuse to translate. With the mappings here,
Cryptol error-message strings translate cleanly and just sit
as opaque `String` values inside `error_unrestricted` calls.
-/

/-- SAW Prelude `appendString`. Maps to Lean's `String.append`. -/
@[reducible] def appendString (a b : String) : String := a ++ b

/-- SAW Prelude `equalString`. Maps to Lean's `String.beq` (the
`BEq String` instance method). Returns SAW's `Bool` (= Lean's
native `Bool`). -/
@[reducible] def equalString (a b : String) : Bool := a == b

/-- SAW Prelude `bytesToString`. Cryptol byte sequence (`Vec n
(Vec 8 Bool)`, MSB-first per byte) → SAW `String`. Each byte
goes through `vecToBitVec` → `BitVec.toNat` → `Char.ofNat`,
folded into a `String`. Behaves correctly for ASCII byte values
(< 128); for high bytes (≥ 128) the resulting `Char` may not be
a valid UTF-8 scalar, but SAW only uses this primitive for
diagnostic `error` messages where any concrete representation
is acceptable. -/
noncomputable def bytesToString (n : Nat) (v : CryptolToLean.SAWCoreVectors.Vec n (CryptolToLean.SAWCoreVectors.Vec 8 Bool)) : String :=
  v.foldr (fun byte acc =>
    String.singleton (Char.ofNat (vecToBitVec byte).toNat) ++ acc)
    ""

end CryptolToLean.SAWCorePrimitives
