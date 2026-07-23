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

/-- SAWCore Prelude `Bit : sort 0`. SAW's bit type is represented by
Lean's `Bool`; keep the realization in the checked support library rather
than as a Haskell-side replacement. -/
@[reducible] def Bit : Type := Bool

/-- SAWCore Prelude `Either a b` — standard coproduct. Matches
Lean's standard sum but defined here so the SAWCore translator can
emit `@CryptolToLean.SAWCorePrimitives.Either.Left …` without
importing Lean's `Sum`. Sort-polymorphic (2026-07-19, mirroring
Lean's `PSum` universe signature): SAWCore's `Either` is applied at
PROPS as well as data — `natCompareLe : (m n : Nat) -> Either
(IsLtNat m n) (IsLeNat n m)` — because SAWCore Prop embeds in
sort 0. Type-level uses instantiate `u = v = 1` and behave exactly
as the previous monomorphic declaration. -/
inductive Either (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  /-- SAWCore `Left` — the left injection. -/
  | Left  : α → Either α β
  /-- SAWCore `Right` — the right injection. -/
  | Right : β → Either α β

/-- SAWCore Prelude `Maybe a`. Sort-polymorphic for the same reason
as `Either` (`proveLeNat : (x y : Nat) -> Maybe (IsLeNat x y)`
instantiates it at a Prop); mirrors Lean's `Option` at `u = 1`.
Constructor order (Nothing, Just) matches the SAWCore declaration
and is pinned in `SAWCoreCtorOrder`. -/
inductive Maybe (α : Sort u) : Sort (max 1 u) where
  /-- SAWCore `Nothing` — the empty case. -/
  | Nothing : Maybe α
  /-- SAWCore `Just` — the value-carrying case. -/
  | Just    : α → Maybe α

/-- Cryptol Prelude `Num` (from `Cryptol.sawcore`). The marker used
throughout Cryptol's numeric-kind machinery: a finite length (via
`TCNum`) or an infinite stream marker (`TCInf`).

SAWCore's `Nat` is mapped to Lean's native `Nat` at the
'SpecialTreatment' level through reducible constructor helpers, so `TCNum`
takes a Lean `Nat` here. If a future user term exercises SAWCore's
`Nat#rec` with a non-Lean-matching argument order we'll need to
revisit; for now specialization reduces those eliminations away
before the translator sees them. -/
inductive Num : Type where
  /-- Cryptol `TCNum n` — a finite numeric-kind length. -/
  | TCNum : Nat → Num
  /-- Cryptol `TCInf` — the infinite (stream) length marker. -/
  | TCInf : Num

/-! ## Nat constructor wrappers

SAWCore's `Nat` / `Pos` constructors (`Zero`, `NatPos`, `One`,
`Bit0`, `Bit1`, `Succ`) are mapped to Lean's native `Nat` via
`SpecialTreatment`. The translator emits these small one-to-one helpers
instead of computing constructor-chain equivalences in Haskell; Lean reduces
the helpers when a concrete numeral is needed. -/

/-- SAWCore `Zero : Nat` constructor. -/
@[simp, reducible] def zero_macro : Nat := 0
/-- SAWCore `One : Pos` constructor. -/
@[simp, reducible] def one_macro : Nat := 1
/-- SAWCore `Succ : Nat → Nat` constructor. -/
@[simp, reducible] def succ_macro (n : Nat) : Nat := Nat.succ n
/-- SAWCore `Bit0 : Pos → Pos` constructor — doubles the numeral. -/
@[simp, reducible] def bit0_macro (n : Nat) : Nat := 2 * n
/-- SAWCore `Bit1 : Pos → Pos` constructor — doubles and adds one. -/
@[simp, reducible] def bit1_macro (n : Nat) : Nat := 2 * n + 1
/-- SAWCore `NatPos : Pos → Nat` constructor — the injection is the
identity because both map to Lean's `Nat`. -/
@[simp, reducible] def natPos_macro (n : Nat) : Nat := n

/-- SAWCore Prelude `Stream a` — infinite sequences of `a`. The
single constructor `MkStream : (Nat → a) → Stream a` packages an
indexed view of the stream. -/
inductive Stream (α : Type) : Type where
  /-- SAWCore `MkStream` — packages the index function. -/
  | MkStream : (Nat → α) → Stream α

/-- Cryptol's `seq n α` carrier at the Lean support-library level. Finite
widths are vectors; the infinite case is the SAW stream representation. Keeping
this as a Lean definition lets wrapper contracts for Cryptol entry points
reason by cases on `Num` inside Lean rather than asking Haskell to compute
width refinements. -/
@[reducible] def seq : Num → Type → Type
  | Num.TCNum n, α => Vec n α
  | Num.TCInf, α => Stream α

/-- Cryptol's `seq n Bool` — the bit-sequence carrier (`seq` at
element type `Bool`). -/
@[reducible] def seqBool (n : Num) : Type := seq n Bool

/-- SAWCore Prelude `EmptyType : sort 0` — the "end of record"
marker. Has one constructor `Empty`; Cryptol's records are encoded
as right-nested `RecordType` chains ending in `EmptyType` / `Empty`.
-/
inductive EmptyType : Type where
  /-- SAWCore `Empty` — the sole inhabitant. -/
  | Empty : EmptyType

/-- SAWCore Prelude `RecordType` — a one-field record builder. Paired
with `RecordValue` as the single constructor. Cryptol uses nested
`RecordType` for multi-field records. -/
inductive RecordType (s : String) (α β : Type) : Type where
  /-- SAWCore `RecordValue` — one field value plus the record tail. -/
  | RecordValue : α → β → RecordType s α β

/-- SAWCore Prelude `UnitType` — the singleton type. SAWCore tuples
desugar to nested `PairType` chains terminating at `UnitType`. -/
inductive UnitType : Type where
  /-- SAWCore `Unit` — the sole inhabitant. -/
  | Unit : UnitType

/-- SAWCore Prelude `PairType` — the basic product. Multi-element
SAWCore tuples are right-nested `PairType` chains terminating at
`UnitType`. -/
inductive PairType (α β : Type) : Type where
  /-- SAWCore `PairValue` — the pair constructor. -/
  | PairValue : α → β → PairType α β

/-- Projection from a SAWCore pair. Phase 8: structural def
matching SAWCore's `Pair_fst = Pair__rec α β (\\_ => α) (\\x _ => x)`.
SAWCore Prelude's `Pair_fst` is the user-facing name and the
SpecialTreatment routes to it directly. -/
def Pair_fst (α β : Type) : PairType α β → α
  | PairType.PairValue a _ => a

/-- Projection from a SAWCore pair — the `Pair_snd` analogue of
`Pair_fst` above. -/
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
through `Int.fmod` (floor modulus). Each function is `@[reducible]`
so SAW-named goals reduce transparently to Int arithmetic.

`n = 0` CAVEAT (corrected 2026-07-23 — the earlier "SAW's
convention is no reduction" claim here was FALSE): SAW's concrete
evaluator is PARTIAL at `Z 0` — `toIntModOp` computes Haskell
`x mod 0`, which THROWS (SAWCore.Simulator.Concrete), so no
SAW-observable `Z 0` value exists. These realizations are total at
`n = 0` (`Int.fmod x 0 = x`), a divergence-at-crash-point pinned by
`differential/intmod_zero_boundary`. Reachable only from raw
SAWCore (Cryptol's `Z n` requires `n >= 1`); the gate-vs-caveat
disposition is a recorded open decision.

The signatures match `Prelude.sawcore` lines 2126-2135 exactly. -/

/-- SAWCore `IntMod n` — Cryptol's `Z n`, represented as `Int` with
every value implicitly reduced mod `n` (see the section comment). -/
@[reducible] def IntMod : Nat → Type := fun _ => Int
/-- SAWCore `toIntMod` — inject an `Int` into `Z n` by reducing. -/
@[reducible] def toIntMod : (n : Nat) → Int → IntMod n := fun n x => Int.fmod x n
/-- SAWCore `fromIntMod` — the canonical representative in `[0, n)`
(floor modulus; identity at `n = 0`, where SAW itself has no value —
see the section's `n = 0` caveat). -/
@[reducible] def fromIntMod : (n : Nat) → IntMod n → Int := fun n x => Int.fmod x n
/-- SAWCore `intModEq` — equality in `Z n`, decided on canonical
representatives. -/
@[reducible] def intModEq : (n : Nat) → IntMod n → IntMod n → Bool :=
  fun n x y => decide (Int.fmod x n = Int.fmod y n)
/-- SAWCore `intModAdd` — addition in `Z n`. -/
@[reducible] def intModAdd : (n : Nat) → IntMod n → IntMod n → IntMod n :=
  fun n x y => Int.fmod (x + y) n
/-- SAWCore `intModSub` — subtraction in `Z n`. -/
@[reducible] def intModSub : (n : Nat) → IntMod n → IntMod n → IntMod n :=
  fun n x y => Int.fmod (x - y) n
/-- SAWCore `intModMul` — multiplication in `Z n`. -/
@[reducible] def intModMul : (n : Nat) → IntMod n → IntMod n → IntMod n :=
  fun n x y => Int.fmod (x * y) n
/-- SAWCore `intModNeg` — negation in `Z n`. -/
@[reducible] def intModNeg : (n : Nat) → IntMod n → IntMod n :=
  fun n x => Int.fmod (-x) n

/-! ## Rational (Phase 6 → Phase 9 follow-up)

SAW Prelude's `Rational` quotient type. Bound to Lean's core
`Rat` type. Operations route through Lean's `Rat` arithmetic;
`ratio a b` is `Rat.mk` (or `a / b` over `Rat`), `rationalRecip`
is reciprocal. -/

/-- SAWCore `Rational` — bound to Lean core's `Rat`. -/
@[reducible] def Rational : Type := Rat
/-- SAWCore `rationalZero` — the rational `0`. -/
@[reducible] def rationalZero : Rational := 0
/-- SAWCore `ratio a b` — the quotient `a / b` over `Rat`. -/
@[reducible] def ratio : Int → Int → Rational := fun a b => (a : Rat) / (b : Rat)
/-- Checked `ratio` — the emitted form when the nonzero-denominator
precondition is discharged as a proof-carrying obligation. -/
@[reducible] def ratio_checkedM (a b : Except String Int)
    (_h : Not (b = Pure.pure 0)) : Except String Rational := do
  let a' ← a
  let b' ← b
  Pure.pure (ratio a' b')
/-- SAWCore `rationalEq` — decidable rational equality as `Bool`. -/
@[reducible] def rationalEq : Rational → Rational → Bool := fun a b => decide (a = b)
/-- SAWCore `rationalLe` — decidable `≤` as `Bool`. -/
@[reducible] def rationalLe : Rational → Rational → Bool := fun a b => decide (a ≤ b)
/-- SAWCore `rationalLt` — decidable `<` as `Bool`. -/
@[reducible] def rationalLt : Rational → Rational → Bool := fun a b => decide (a < b)
/-- SAWCore `rationalAdd` — rational addition. -/
@[reducible] def rationalAdd : Rational → Rational → Rational := fun a b => a + b
/-- SAWCore `rationalSub` — rational subtraction. -/
@[reducible] def rationalSub : Rational → Rational → Rational := fun a b => a - b
/-- SAWCore `rationalMul` — rational multiplication. -/
@[reducible] def rationalMul : Rational → Rational → Rational := fun a b => a * b
/-- SAWCore `rationalNeg` — rational negation. -/
@[reducible] def rationalNeg : Rational → Rational := fun a => -a
/-- SAWCore `rationalRecip` — rational reciprocal (`Rat` convention:
`0⁻¹ = 0`; the partiality contract lives in the checked/runtime
variants below). -/
@[reducible] def rationalRecip : Rational → Rational := fun a => a⁻¹
/-- Checked `rationalRecip` — the emitted form when the nonzero
precondition is discharged as a proof-carrying obligation. -/
@[reducible] def rationalRecip_checkedM (a : Except String Rational)
    (_h : Not (a = Pure.pure 0)) : Except String Rational := do
  let a' ← a
  Pure.pure (rationalRecip a')
/-- Runtime-checked `ratio` — the emitted form when the
nonzero-denominator bound is NOT derivable at the emission site
(OP-2); a zero denominator is a visible `Except` error. -/
@[reducible] def ratio_runtimeM (a b : Except String Int) :
    Except String Rational := do
  let a' ← a
  let b' ← b
  if b' = 0 then throw "ratio: zero denominator"
  else Pure.pure (ratio a' b')
/-- Runtime-checked `rationalRecip` — see `ratio_runtimeM`. -/
@[reducible] def rationalRecip_runtimeM (a : Except String Rational) :
    Except String Rational := do
  let a' ← a
  if a' = 0 then throw "rationalRecip: reciprocal of zero"
  else Pure.pure (rationalRecip a')
/-- SAWCore `rationalFloor` — floor to `Int`. -/
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

/-- SAWCore `Float` — bound as a mantissa-exponent `Int × Int` pair
(see the section comment for why any inhabited type is faithful).
Emitted FULLY QUALIFIED: the short name ties with Lean core's
`_root_.Float` (`mapsToQualifiedTie`, SpecialTreatment.hs). -/
@[reducible] def Float : Type := Int × Int
/-- SAWCore `mkFloat` — the mantissa-exponent constructor. -/
@[reducible] def mkFloat : Int → Int → Float := fun m e => (m, e)
/-- SAWCore `Double` — same `Int × Int` binding as `Float`. -/
@[reducible] def Double : Type := Int × Int
/-- SAWCore `mkDouble`. N.B.: SAW's own declaration returns `Float`,
not `Double` — see `saw-core/prelude/Prelude.sawcore:2163`. Faithful
binding. -/
@[reducible] def mkDouble : Int → Int → Float := fun m e => (m, e)

/-! ## Arithmetic primitives

These are declared as reducible wrappers over Lean's native
arithmetic rather than opaque axioms. Definitional equality of
arithmetic is needed for type-checking vector sizes (e.g.
Cryptol's `[0..10]` has length `addNat 1 (subNat 10 0)` which Lean
must recognise as `11` to match a `Vec 11` annotation).

SAWCore's `subNat` saturates at zero (`subNat n m = max 0 (n - m)`);
Lean's `Nat.sub` has the same truncated-subtraction semantics. -/

/-- SAWCore `addNat` — Nat addition. -/
@[reducible] def addNat : Nat → Nat → Nat := Nat.add
/-- SAWCore `subNat` — saturating Nat subtraction (see the section
comment: SAW and Lean agree on truncation at zero). -/
@[reducible] def subNat : Nat → Nat → Nat := Nat.sub
/-- SAWCore Prelude `eqNat x y = Eq Nat x y` — the Prop-valued Nat
equality alias (2026-07-19, IsLeNat/bv-order obligation family).
Reducible so consumers see the underlying `Eq` definitionally. -/
@[reducible] def eqNat (x y : Nat) : Prop := @Eq Nat x y

/-- SAWCore Prelude `primitive proveLeNat : (x y : Nat) -> Maybe
(IsLeNat x y)`. NO implementation exists anywhere in SAW — neither
the simulator nor the Rocq backend realizes it (repo-wide: zero
references outside the Prelude declaration), so the primitive is
TYPING-ONLY and any inhabitant is unfalsifiable against SAW
semantics. This realization is the canonical decision procedure:
`Just` exactly when `x ≤ y`, carrying the actual proof. SAWCore
`IsLeNat` maps to `Nat.le` — structurally identical inductives
(base at `n`; step to `Succ m`). -/
def proveLeNat (x y : Nat) : Maybe (Nat.le x y) :=
  if h : x ≤ y then Maybe.Just h else Maybe.Nothing

/-- SAWCore Prelude `primitive natCompareLe : (m n : Nat) -> Either
(IsLtNat m n) (IsLeNat n m)`. Same status as `proveLeNat`
(typing-only, no SAW-side realization anywhere); the canonical
total comparison. SAWCore `IsLtNat m n = IsLeNat (Succ m) n` maps
to `Nat.lt` definitionally. -/
def natCompareLe (m n : Nat) : Either (Nat.lt m n) (Nat.le n m) :=
  if h : m < n then Either.Left h else Either.Right (Nat.le_of_not_lt h)

/-- SAWCore `minNat` — Nat minimum. -/
@[reducible] def minNat : Nat → Nat → Nat := Nat.min
/-- SAWCore `maxNat` — Nat maximum. -/
@[reducible] def maxNat : Nat → Nat → Nat := Nat.max
/-- SAWCore `mulNat` — Nat multiplication. -/
@[reducible] def mulNat : Nat → Nat → Nat := Nat.mul
/-- SAWCore `expNat` — Nat exponentiation. -/
@[reducible] def expNat : Nat → Nat → Nat := fun m n => Nat.pow m n
/-- SAWCore `doubleNat` — `2 * n`. -/
@[reducible] def doubleNat : Nat → Nat := fun n => 2 * n
/-- SAWCore `pred` — saturating predecessor (`pred 0 = 0`, matching
SAW's `Nat` case analysis). -/
@[reducible] def pred     : Nat → Nat := Nat.pred
/-- SAW Prelude `divNat x y = (divModNat x y).0` — AT NONZERO
DIVISORS ONLY. SAWCore division by zero is genuinely undefined
(concrete simulator crashes on Haskell `divMod`; symbolic routes to
SMT all-ones), while `Nat.div x 0 = 0` is total: the zero points
DIVERGE. Emission never reaches this def unguarded — full-arity
sites go through `divNat_checked` (proven nonzero) and
under-applied sites through `divNat_runtimeM` (throws at zero);
see doc/2026-07-18_underapplied-partial-op-wrapper.md. -/
@[reducible] def divNat : Nat → Nat → Nat := Nat.div
/-- Checked `divNat` — the emitted form at full arity, with the
nonzero-divisor precondition discharged as a proof-carrying
obligation. -/
@[reducible] def divNat_checked (x y : Nat) (_h : Not (y = 0)) : Nat :=
  divNat x y
/-- SAW Prelude `modNat x y = (divModNat x y).1` — at nonzero
divisors only; same zero-point caveat as `divNat`. -/
@[reducible] def modNat : Nat → Nat → Nat := Nat.mod
/-- Checked `modNat` — see `divNat_checked`. -/
@[reducible] def modNat_checked (x y : Nat) (_h : Not (y = 0)) : Nat :=
  modNat x y
/-- SAW Prelude primitive `divModNat : Nat -> Nat -> Nat * Nat`.
Returns (quotient, remainder) — at nonzero divisors only; same
zero-point caveat as `divNat`. -/
@[reducible] def divModNat : Nat → Nat → PairType Nat (PairType Nat UnitType) :=
  fun x y =>
    PairType.PairValue (Nat.div x y)
      (PairType.PairValue (Nat.mod x y) UnitType.Unit)
/-- Checked `divModNat` — see `divNat_checked`. -/
@[reducible] def divModNat_checked (x y : Nat) (_h : Not (y = 0)) :
    PairType Nat (PairType Nat UnitType) :=
  divModNat x y

/-! Under-applied partial-op RUNTIME wrappers (2026-07-18 design +
audit, doc/2026-07-18_underapplied-partial-op-wrapper.md). These are
the function VALUES a contract-bearing partial op lowers to when it
appears at less than contract arity (dictionary fields, partial
applications). Signature = the translated dictionary-field slot
type: all-Except value args, NO proof argument. Every wrapper
THROWS at the contract-excluded point — division by zero is
genuinely undefined in SAWCore (concrete crash, symbolic
unconstrained), so a throw is the only sound representation; the
nonzero branch is defeq-identical to the matching *_checked(M)
body so both representations agree away from zero. -/
/-- Under-applied `divNat` runtime wrapper (see the block comment
above for the contract). -/
@[reducible] def divNat_runtimeM (x y : Except String Nat) :
    Except String Nat := do
  let x' ← x
  let y' ← y
  if y' = 0 then throw "divNat: division by zero"
  else Pure.pure (divNat x' y')
/-- Under-applied `modNat` runtime wrapper — see `divNat_runtimeM`. -/
@[reducible] def modNat_runtimeM (x y : Except String Nat) :
    Except String Nat := do
  let x' ← x
  let y' ← y
  if y' = 0 then throw "modNat: division by zero"
  else Pure.pure (modNat x' y')
/-- Under-applied `divModNat` runtime wrapper — see
`divNat_runtimeM`. -/
@[reducible] def divModNat_runtimeM (x y : Except String Nat) :
    Except String (PairType Nat (PairType Nat UnitType)) := do
  let x' ← x
  let y' ← y
  if y' = 0 then throw "divModNat: division by zero"
  else Pure.pure (divModNat x' y')

/-- Bridging lemmas for `omega`: it recognizes `x / k` / `x % k` only
through the `HDiv.hDiv` / `HMod.hMod` spelling and atomizes bare
`Nat.div` / `Nat.mod` applications (the same way it atomizes
`Nat.sub`), so the emitted evidence chains rewrite the SAW aliases —
including the proof-carrying checked forms — to the operator spelling
before running `omega`. All are definitional. -/
theorem divNat_eq_div (x y : Nat) : divNat x y = x / y := rfl
theorem modNat_eq_mod (x y : Nat) : modNat x y = x % y := rfl
theorem divNat_checked_eq_div (x y : Nat) (h : Not (y = 0)) :
    divNat_checked x y h = x / y := rfl
theorem modNat_checked_eq_mod (x y : Nat) (h : Not (y = 0)) :
    modNat_checked x y h = x % y := rfl

/-- SAWCore Prelude `if0Nat α n x y`: returns `x` when `n = 0` and
`y` otherwise. SAW defines this with `Nat#rec` over its binary Nat
encoding; after the translator maps SAW Nat to Lean Nat, the same
case split is Lean's ordinary zero test. -/
@[reducible] def if0NatRaw.{u} (α : Sort u) (n : Nat) (x y : α) : α :=
  if n = 0 then x else y

/-- Value-domain `if0Nat` — the wrapped form of `if0NatRaw`: both
branches carry the `Except` carrier, and the select keeps whichever
branch's effect fires (the scrutinee `n` is a raw index, never
wrapped). -/
@[reducible] def if0NatM.{u} (α : Type u) (n : Nat)
    (x y : Except String α) : Except String α :=
  if n = 0 then x else y

/-- SAWCore Prelude `natCase p z s n` — the non-recursive Nat case
split (`Nat__rec` discarding the recursive result). Emitted only for
raw motives (type/index/proof); value-domain motives reject at
translation with a named diagnostic. The successor arm receives the
predecessor. -/
@[reducible] def natCaseRaw.{u} (p : Nat → Sort u)
    (z : p 0) (s : (n : Nat) → p (n + 1)) : (n : Nat) → p n
  | 0 => z
  | n + 1 => s n

/-- SAWCore `widthNat n` — the number of bits to represent `n`.
`widthNat 0 = 0`, `widthNat 1 = 1`, `widthNat 2 = widthNat 3 = 2`,
... matches Lean's `Nat.log2 n + 1` for n > 0, with 0 special-cased
to 0 (Lean's `Nat.log2 0 = 0` would give 1 without the guard). -/
@[reducible] def widthNat : Nat → Nat := fun n =>
  if n = 0 then 0 else Nat.log2 n + 1

-- Comparison wrappers — reducible aliases over Lean's native Nat
-- comparisons. These are only sound because we've already
-- committed to SAW Nat ≡ Lean Nat at the value level.
/-- SAWCore `equalNat` — Bool-valued Nat equality. -/
@[reducible] def equalNat : Nat → Nat → Bool := fun a b => decide (a = b)
/-- SAWCore `ltNat` — Bool-valued Nat `<`. -/
@[reducible] def ltNat    : Nat → Nat → Bool := fun a b => decide (a < b)
/-- SAWCore `leNat` — Bool-valued Nat `≤`. -/
@[reducible] def leNat    : Nat → Nat → Bool := fun a b => decide (a ≤ b)

/-! ### Integer ops (Phase 9 follow-up: defined via Lean's `Int`)

SAW's concrete simulator (`SAWCore.Simulator.Concrete`) defines
`bpIntDiv = Haskell div` and `bpIntMod = Haskell mod`, which are
**floor** division/modulus (non-negative remainder for positive
divisor). This corresponds to Lean's `Int.fdiv` / `Int.fmod`,
NOT `Int.div` / `Int.mod` (which are truncated) — AT NONZERO
DIVISORS ONLY: Haskell div/mod by zero crashes while fdiv/fmod are
total (`fdiv x 0 = 0`, `fmod x 0 = x`), so the zero points diverge
and emission only reaches these through the checked/runtime gates
(doc/2026-07-18_underapplied-partial-op-wrapper.md). -/
/-- SAWCore `intAdd` — Int addition. -/
@[reducible] def intAdd : Int → Int → Int := fun a b => a + b
/-- SAWCore `intSub` — Int subtraction. -/
@[reducible] def intSub : Int → Int → Int := fun a b => a - b
/-- SAWCore `intMul` — Int multiplication. -/
@[reducible] def intMul : Int → Int → Int := fun a b => a * b
/-- SAWCore `intDiv` — FLOOR division (see the section comment: SAW's
concrete simulator is Haskell `div`), at nonzero divisors only. -/
@[reducible] def intDiv : Int → Int → Int := Int.fdiv
/-- Checked `intDiv` — the emitted form with the nonzero-divisor
precondition discharged as a proof-carrying obligation. -/
@[reducible] def intDiv_checkedM (x y : Except String Int)
    (_h : Not (y = Pure.pure 0)) : Except String Int := do
  let x' ← x
  let y' ← y
  Pure.pure (intDiv x' y')
/-- SAWCore `intMod` — FLOOR modulus (Haskell `mod`), at nonzero
divisors only. -/
@[reducible] def intMod : Int → Int → Int := Int.fmod
/-- Checked `intMod` — see `intDiv_checkedM`. -/
@[reducible] def intMod_checkedM (x y : Except String Int)
    (_h : Not (y = Pure.pure 0)) : Except String Int := do
  let x' ← x
  let y' ← y
  Pure.pure (intMod x' y')
/-- Under-applied `intDiv` runtime wrapper — throws at the
contract-excluded zero divisor (see `divNat_runtimeM`). -/
@[reducible] def intDiv_runtimeM (x y : Except String Int) :
    Except String Int := do
  let x' ← x
  let y' ← y
  if y' = 0 then throw "intDiv: division by zero"
  else Pure.pure (intDiv x' y')
/-- Under-applied `intMod` runtime wrapper — see `intDiv_runtimeM`. -/
@[reducible] def intMod_runtimeM (x y : Except String Int) :
    Except String Int := do
  let x' ← x
  let y' ← y
  if y' = 0 then throw "intMod: division by zero"
  else Pure.pure (intMod x' y')
/-- SAWCore `intNeg` — Int negation. -/
@[reducible] def intNeg : Int → Int := fun a => -a
-- intAbs/intMin/intMax (2026-07-20): SAW's concrete simulator is
-- Haskell abs/min/max on unbounded Integer (Concrete.hs
-- bpIntAbs/bpIntMin/bpIntMax) — these are the exact Lean
-- counterparts (total; no bounded-representation edge cases).
/-- SAWCore `intAbs` — absolute value (see the comment above: exact
Haskell `abs` counterpart). -/
@[reducible] def intAbs : Int → Int := fun a => if a < 0 then -a else a
/-- SAWCore `intMin` — Int minimum. -/
@[reducible] def intMin : Int → Int → Int := fun a b => min a b
/-- SAWCore `intMax` — Int maximum. -/
@[reducible] def intMax : Int → Int → Int := fun a b => max a b
/-- SAWCore `intEq` — Bool-valued Int equality. -/
@[reducible] def intEq  : Int → Int → Bool := fun a b => decide (a = b)
/-- SAWCore `intLe` — Bool-valued Int `≤`. -/
@[reducible] def intLe  : Int → Int → Bool := fun a b => decide (a ≤ b)
/-- SAWCore `intLt` — Bool-valued Int `<`. -/
@[reducible] def intLt  : Int → Int → Bool := fun a b => decide (a < b)
/-- SAWCore `natToInt` — the canonical injection. -/
@[reducible] def natToInt : Nat → Int := Int.ofNat
/-- SAWCore `intToNat` — clamps negatives to `0`
(`Prelude.sawcore:2105` "intToNat x == max 0 x"; the concrete
simulator's `intToNatOp` returns `VNat 0` for `x < 0`). `Int.toNat`
has exactly this semantics. -/
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

A few ops stay as direct wrappers even though their proof-library coherence is
non-trivial enough to defer to focused follow-up:

  - `bvSExt`: SAW's `bvSExt m n : Vec (n+1) Bool → Vec (m + (n+1))
    Bool` has a length shape Lean's `BitVec.signExtend` doesn't
    quite match. Coherence needs the length arithmetic worked
    through. Stays axiomatic.
  - `bvPopcount` / `bvCountLeadingZeros` / `bvCountTrailingZeros` /
    `bvLg2`: Lean has `BitVec.toNat`-based equivalents but broader theorem
    coherence is bit-level rather than int-level. Deferred.

The non-primitive bv ops (`bvNot`, `bvAnd`, `bvOr`, `bvXor`,
`bvEq`) are SAWCore Prelude /defs/ rather than primitives — their
bodies use `map` / `bvZipWith` / `vecEq` over individual `Bool`
ops. We keep them opaque via `leanOpaqueBuiltins` (in
`SAWCentral.Prover.Exporter`) so normalization doesn't expose the
inner machinery, then provide top-level defs here that route
through `BitVec`. -/

/-- SAWCore `bvNat n k` — the width-`n` bitvector with value
`k mod 2^n` (big-endian `Vec n Bool` surface, `BitVec` internals). -/
noncomputable def bvNat (n : Nat) (k : Nat) : Vec n Bool :=
  bitVecToVec (BitVec.ofNat n k)
/-- Bitvector nonzero predicate used by proof-carrying division/remainder
helpers. Spelling this once keeps generated contracts stable while preserving
the SAW surface representation as `Vec n Bool`. -/
@[reducible] def bvNonzero (n : Nat) (v : Vec n Bool) : Prop :=
  Not (v = bvNat n 0)
/-- `bvNonzero` at the wrapped carrier — the precondition spelling
the checked division/remainder helpers take. -/
@[reducible] def bvNonzeroM (n : Nat) (v : Except String (Vec n Bool)) : Prop :=
  Not (v = Pure.pure (bvNat n 0))
/-- SAWCore `bvToNat` — the unsigned value. -/
noncomputable def bvToNat (n : Nat) (v : Vec n Bool) : Nat :=
  (vecToBitVec v).toNat
/-- SAWCore `bvToInt` — the UNSIGNED value
(`Prelude.sawcore:2113` "return the unsigned value"; the concrete
simulator's `bvToIntOp` is `unsigned`, Concrete.hs). Realized as
`BitVec.toNat` injected into `Int` — NOT `BitVec.toInt`, which is
the signed conversion and belongs to `sbvToInt` only. (2026-07-23
soundness fix: both conversions were `.toInt`, so `bvToInt`
diverged from SAW on every sign-bit-set input — found by audit;
the differential row now pins a sign-crossing case.) -/
noncomputable def bvToInt (n : Nat) (v : Vec n Bool) : Int :=
  Int.ofNat (vecToBitVec v).toNat
/-- SAWCore `intToBv` — `k mod 2^n` for `k ≥ 0`, two's-complement
encoding for `k < 0` (`BitVec.ofInt`). -/
noncomputable def intToBv (n : Nat) (k : Int) : Vec n Bool :=
  bitVecToVec (BitVec.ofInt n k)
/-- SAWCore `sbvToInt` — the 2's-complement SIGNED value
(`Prelude.sawcore:2116`; the concrete simulator's `sbvToIntOp` is
`signed`). `BitVec.toInt` is exactly this. -/
noncomputable def sbvToInt (n : Nat) (v : Vec n Bool) : Int :=
  (vecToBitVec v).toInt

/-- SAWCore `bvAdd` — modular bitvector addition. -/
noncomputable def bvAdd (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) + (vecToBitVec y))
/-- SAWCore `bvSub` — modular bitvector subtraction. -/
noncomputable def bvSub (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) - (vecToBitVec y))
/-- SAWCore `bvMul` — modular bitvector multiplication. -/
noncomputable def bvMul (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) * (vecToBitVec y))
/-- SAWCore `bvNeg` — two's-complement negation. -/
noncomputable def bvNeg (n : Nat) (x : Vec n Bool) : Vec n Bool :=
  bitVecToVec (- (vecToBitVec x))
/-- SAWCore `bvUDiv` — unsigned division (`BitVec.udiv`), at nonzero
divisors only; emission reaches it through the checked/runtime
gates. -/
noncomputable def bvUDiv (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x).udiv (vecToBitVec y))
/-- Checked `bvUDiv` — the emitted form with the nonzero-divisor
precondition discharged as a proof-carrying obligation. -/
noncomputable def bvUDiv_checkedM (n : Nat)
    (x y : Except String (Vec n Bool)) (_h : bvNonzeroM n y) :
    Except String (Vec n Bool) := do
  let x' ← x
  let y' ← y
  Pure.pure (bvUDiv n x' y')
/-- SAWCore `bvURem` — unsigned remainder (`BitVec.umod`), at
nonzero divisors only. -/
noncomputable def bvURem (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x).umod (vecToBitVec y))
/-- Checked `bvURem` — see `bvUDiv_checkedM`. -/
noncomputable def bvURem_checkedM (n : Nat)
    (x y : Except String (Vec n Bool)) (_h : bvNonzeroM n y) :
    Except String (Vec n Bool) := do
  let x' ← x
  let y' ← y
  Pure.pure (bvURem n x' y')

/-- SAWCore `bvSDiv` — signed division (`BitVec.sdiv`; SAW's width
shape `Vec (n+1) Bool` guarantees positive width), at nonzero
divisors only. -/
noncomputable def bvSDiv (n : Nat) (x y : Vec (n + 1) Bool) : Vec (n + 1) Bool :=
  bitVecToVec ((vecToBitVec x).sdiv (vecToBitVec y))
/-- Checked `bvSDiv` — see `bvUDiv_checkedM`. -/
noncomputable def bvSDiv_checkedM (n : Nat)
    (x y : Except String (Vec (n + 1) Bool)) (_h : bvNonzeroM (n + 1) y) :
    Except String (Vec (n + 1) Bool) := do
  let x' ← x
  let y' ← y
  Pure.pure (bvSDiv n x' y')
/-- SAWCore `bvSRem` — signed remainder (`BitVec.srem`), at nonzero
divisors only. -/
noncomputable def bvSRem (n : Nat) (x y : Vec (n + 1) Bool) : Vec (n + 1) Bool :=
  bitVecToVec ((vecToBitVec x).srem (vecToBitVec y))
/-- Checked `bvSRem` — see `bvUDiv_checkedM`. -/
noncomputable def bvSRem_checkedM (n : Nat)
    (x y : Except String (Vec (n + 1) Bool)) (_h : bvNonzeroM (n + 1) y) :
    Except String (Vec (n + 1) Bool) := do
  let x' ← x
  let y' ← y
  Pure.pure (bvSRem n x' y')

/-- Under-applied `bvUDiv` runtime wrapper — throws at the
contract-excluded zero divisor (see `divNat_runtimeM`). -/
noncomputable def bvUDiv_runtimeM (n : Nat)
    (x y : Except String (Vec n Bool)) : Except String (Vec n Bool) := do
  let x' ← x
  let y' ← y
  if vecToBitVec y' = 0 then throw "bvUDiv: division by zero"
  else Pure.pure (bvUDiv n x' y')
/-- Under-applied `bvURem` runtime wrapper — see `bvUDiv_runtimeM`. -/
noncomputable def bvURem_runtimeM (n : Nat)
    (x y : Except String (Vec n Bool)) : Except String (Vec n Bool) := do
  let x' ← x
  let y' ← y
  if vecToBitVec y' = 0 then throw "bvURem: division by zero"
  else Pure.pure (bvURem n x' y')
/-- Under-applied `bvSDiv` runtime wrapper — see `bvUDiv_runtimeM`. -/
noncomputable def bvSDiv_runtimeM (n : Nat)
    (x y : Except String (Vec (n + 1) Bool)) :
    Except String (Vec (n + 1) Bool) := do
  let x' ← x
  let y' ← y
  if vecToBitVec y' = 0 then throw "bvSDiv: division by zero"
  else Pure.pure (bvSDiv n x' y')
/-- Under-applied `bvSRem` runtime wrapper — see `bvUDiv_runtimeM`. -/
noncomputable def bvSRem_runtimeM (n : Nat)
    (x y : Except String (Vec (n + 1) Bool)) :
    Except String (Vec (n + 1) Bool) := do
  let x' ← x
  let y' ← y
  if vecToBitVec y' = 0 then throw "bvSRem: division by zero"
  else Pure.pure (bvSRem n x' y')

/-- Nonzero contract for Cryptol signed bitvector division/modulus wrappers.
Only finite positive widths are admissible for the checked helper. The zero
width and infinite stream branches are impossible under this contract, which
keeps those source-surface error cases from being silently totalized. -/
@[reducible] def ecSignedBVNonzeroM (n : Num)
    (v : Except String (seqBool n)) : Prop :=
  match n with
  | Num.TCNum 0 => False
  | Num.TCNum (Nat.succ w) => bvNonzeroM (Nat.succ w) v
  | Num.TCInf => False

/-- Checked Cryptol `ecSDiv` (`Cryptol.sawcore`) — dispatches on the
`Num` width; only finite positive widths are reachable under the
`ecSignedBVNonzeroM` contract. -/
noncomputable def ecSDiv_checkedM (n : Num)
    (x y : Except String (seqBool n)) (h : ecSignedBVNonzeroM n y) :
    Except String (seqBool n) :=
  match n with
  | Num.TCNum 0 => False.elim h
  | Num.TCNum (Nat.succ w) => bvSDiv_checkedM w x y h
  | Num.TCInf => False.elim h

/-- Checked Cryptol `ecSMod` — see `ecSDiv_checkedM`. -/
noncomputable def ecSMod_checkedM (n : Num)
    (x y : Except String (seqBool n)) (h : ecSignedBVNonzeroM n y) :
    Except String (seqBool n) :=
  match n with
  | Num.TCNum 0 => False.elim h
  | Num.TCNum (Nat.succ w) => bvSRem_checkedM w x y h
  | Num.TCInf => False.elim h

/-- Under-applied Cryptol `ecSDiv` runtime wrapper — every
contract-excluded branch (zero width, infinite width, zero divisor
via `bvSDiv_runtimeM`) throws visibly. -/
noncomputable def ecSDiv_runtimeM (n : Num)
    (x y : Except String (seqBool n)) : Except String (seqBool n) :=
  match n with
  | Num.TCNum 0 => throw "ecSDiv: zero-width signed division"
  | Num.TCNum (Nat.succ w) => bvSDiv_runtimeM w x y
  | Num.TCInf => throw "ecSDiv: infinite-width signed division"
/-- Under-applied Cryptol `ecSMod` runtime wrapper — see
`ecSDiv_runtimeM`. -/
noncomputable def ecSMod_runtimeM (n : Num)
    (x y : Except String (seqBool n)) : Except String (seqBool n) :=
  match n with
  | Num.TCNum 0 => throw "ecSMod: zero-width signed modulus"
  | Num.TCNum (Nat.succ w) => bvSRem_runtimeM w x y
  | Num.TCInf => throw "ecSMod: infinite-width signed modulus"

/-- SAWCore `bvShl` — logical left shift (zero fill). -/
noncomputable def bvShl (w : Nat) (x : Vec w Bool) (i : Nat) : Vec w Bool :=
  bitVecToVec ((vecToBitVec x) <<< i)
/-- SAWCore `bvShr` — logical right shift (zero fill). -/
noncomputable def bvShr (w : Nat) (x : Vec w Bool) (i : Nat) : Vec w Bool :=
  bitVecToVec ((vecToBitVec x) >>> i)

/-- SAWCore `bvSShr` — arithmetic right shift (sign fill; SAW's
width shape guarantees a sign bit exists). -/
noncomputable def bvSShr (w : Nat) (x : Vec (w + 1) Bool) (i : Nat) : Vec (w + 1) Bool :=
  bitVecToVec ((vecToBitVec x).sshiftRight i)

/-- SAWCore `bvNot` — bitwise complement. -/
noncomputable def bvNot (n : Nat) (x : Vec n Bool) : Vec n Bool :=
  bitVecToVec (~~~ (vecToBitVec x))
/-- SAWCore `bvAnd` — bitwise conjunction. -/
noncomputable def bvAnd (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) &&& (vecToBitVec y))
/-- SAWCore `bvOr` — bitwise disjunction. -/
noncomputable def bvOr  (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) ||| (vecToBitVec y))
/-- SAWCore `bvXor` — bitwise exclusive or. -/
noncomputable def bvXor (n : Nat) (x y : Vec n Bool) : Vec n Bool :=
  bitVecToVec ((vecToBitVec x) ^^^ (vecToBitVec y))

/-- SAWCore `bvEq` — Bool-valued bitvector equality. -/
noncomputable def bvEq  (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x) == (vecToBitVec y)
/-- SAWCore `bvult` — unsigned `<`. -/
noncomputable def bvult (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x).ult (vecToBitVec y)

/-- SAWCore Prelude `is_bvult n x y = Eq Bool (bvult n x y) True` —
the Prop-valued bitvector strict-order alias (2026-07-19,
IsLeNat/bv-order obligation family). Reducible so consumers see the
underlying `Eq` definitionally. -/
@[reducible] noncomputable def is_bvult (n : Nat) (x y : Vec n Bool) : Prop :=
  @Eq Bool (bvult n x y) Bool.true

/-- SAWCore `bvule` — unsigned `≤`. -/
noncomputable def bvule (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x).ule (vecToBitVec y)
/-- SAWCore `bvugt` — unsigned `>` (flipped `ult`). -/
noncomputable def bvugt (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec y).ult (vecToBitVec x)
/-- SAWCore `bvuge` — unsigned `≥` (flipped `ule`). -/
noncomputable def bvuge (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec y).ule (vecToBitVec x)
/-- SAWCore `bvslt` — signed `<`. -/
noncomputable def bvslt (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x).slt (vecToBitVec y)
/-- SAWCore `bvsle` — signed `≤`. -/
noncomputable def bvsle (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec x).sle (vecToBitVec y)
/-- SAWCore `bvsgt` — signed `>` (flipped `slt`). -/
noncomputable def bvsgt (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec y).slt (vecToBitVec x)
/-- SAWCore `bvsge` — signed `≥` (flipped `sle`). -/
noncomputable def bvsge (n : Nat) (x y : Vec n Bool) : Bool :=
  (vecToBitVec y).sle (vecToBitVec x)

/-- SAWCore `bvUExt m n` — zero extension to width `m + n`. -/
noncomputable def bvUExt (m n : Nat) (v : Vec n Bool) : Vec (m + n) Bool :=
  bitVecToVec ((vecToBitVec v).zeroExtend (m + n))

/-- SAWCore `bvSExt m n` — sign extension to width `m + (n + 1)`
(SAW's shape guarantees a sign bit to replicate). -/
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

/-- Ceiling of log base 2 of the bv (interpreted as Nat). For input 0, returns
0 by SAW convention. This matches SAW's `lg2rem`-based primitive: powers of two
return their exponent, and non-powers of two round up. -/
noncomputable def bvLg2 (n : Nat) (v : Vec n Bool) : Vec n Bool :=
  let x := (vecToBitVec v).toNat
  bvNat n (if x ≤ 1 then 0 else Nat.log2 (x - 1) + 1)

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

/-- SAWCore `EmptyVec a` — the empty vector (2026-07-20). Defined by
`Fin 0` elimination so it needs no element of `α`. -/
def EmptyVec (α : Type) : Vec 0 α :=
  Vector.ofFn (fun (i : Fin 0) => i.elim0)

/-- SAWCore `head n a v` — first element of a nonempty vector.
Raw definition for RAW-LOGICAL positions only (proof-primitive
obligation statements such as `head_gen`); Phase-β VALUE positions
keep their existing rejection (`SpecialTreatment`: replaced by
`atWithDefault` on the value path). -/
def head (n : Nat) (α : Type) (v : Vec (Nat.succ n) α) : α :=
  v[0]

/-- SAWCore `tail n a v` — drop the first element. Raw definition
for RAW-LOGICAL positions only, mirroring `head`. -/
def tail (n : Nat) (α : Type) (v : Vec (Nat.succ n) α) : Vec n α :=
  Vector.ofFn (fun (i : Fin n) => v[i.val + 1])

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
def genWithBoundsM (n : Nat) (α : Type)
    (f : (i : Nat) → i < n → Except String α) :
    Except String (Vec n α) :=
  Vector.ofFnM (fun (i : Fin n) => f i.val i.isLt)

/-- Wrapped `gen` without a bounds-aware generator — the emitted form
when the element function ignores the in-range fact. Short-circuits
on the first `Except.error` element like `genWithBoundsM`. -/
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

/-! ### Proof-carrying vector operations

These checked helpers realize SAWCore's `*WithProof` vector primitives in the
Phase β `Except` convention. The SAW-side proof arguments are not trusted by
the translator. Instead, generated Lean code must pass kernel-checked evidence
for the corresponding bounds proposition.
-/

/-- Proof-carrying realization of SAWCore's `at`/`atWithProof` — the
emitted form when the bound IS derivable at the emission site: the
index comes with kernel-checked `i < n` evidence, so no runtime test
and no error branch exist. -/
def atWithProof_checkedM (n : Nat) (α : Type)
    (xs : Except String (Vec n α)) (i : Nat) (h : i < n) :
    Except String α := do
  let vec ← xs
  pure vec[i]

/-- Runtime-checked realization of SAWCore's `at` for index positions
whose bound is NOT derivable at the emission site (OP-2,
doc/2026-07-12_obligation-placement-design.md). Faithful, not a
fallback: Prelude defines
`at n a v i = atWithDefault n a (error a "at: index out of bounds") v i`,
so an out-of-range access MEANS this error. The message must stay
byte-for-byte the Prelude string with nothing interpolated — the
`Except String` carrier compares messages, and SAW yields the SAME
error for every out-of-range index, so an index-bearing message would
let Lean distinguish computations SAW deems equal. Where the bound IS
derivable, emission prefers 'atWithProof_checkedM' (the proof-carrying
refinement); this accessor is the honest form everywhere else. -/
def atRuntimeCheckedM (n : Nat) (α : Type)
    (xs : Except String (Vec n α)) (i : Nat) : Except String α := do
  let vec ← xs
  if _h : i < n then pure vec[i]
  else throw "at: index out of bounds"

/- Self-tests: an in-bounds read returns the element; an out-of-range
read fails with EXACTLY the Prelude error string (byte-for-byte, no
index interpolated — see the docstring's carrier-comparison argument);
an incoming error propagates ITSELF, never a manufactured message. -/

/-- info: Except.ok 20 -/
#guard_msgs in
#eval atRuntimeCheckedM 3 Nat (Pure.pure #v[10, 20, 30]) 1

/-- info: Except.error "at: index out of bounds" -/
#guard_msgs in
#eval atRuntimeCheckedM 3 Nat (Pure.pure #v[10, 20, 30]) 3

/-- info: Except.error "boom" -/
#guard_msgs in
#eval atRuntimeCheckedM 3 Nat (Except.error "boom") 1

/-- SAWCore `genWithProof` — the bounds-aware generator IS
`genWithBoundsM`; the separate name keeps the emitted contract
aligned with the SAW primitive it realizes. -/
def genWithProof_checkedM (n : Nat) (α : Type)
    (f : (i : Nat) → i < n → Except String α) :
    Except String (Vec n α) :=
  genWithBoundsM n α f

/-- SAWCore `updWithProof` — pointwise update at a proven-in-range
index. -/
def updWithProof_checkedM (n : Nat) (α : Type)
    (xs : Except String (Vec n α)) (i : Nat) (x : Except String α)
    (_h : i < n) : Except String (Vec n α) := do
  let vec ← xs
  let x' ← x
  pure (Vector.ofFn (fun (j : Fin n) =>
    if _heq : j.val = i then x' else vec[j]))

/-- SAWCore `sliceWithProof` — the length-`len` window at `off`,
with the `off + len ≤ n` bound kernel-checked. -/
def sliceWithProof_checkedM (α : Type) (n off len : Nat)
    (xs : Except String (Vec n α)) (h : off + len <= n) :
    Except String (Vec len α) := do
  let vec ← xs
  pure (Vector.ofFn (fun (j : Fin len) =>
    have hj : off + j.val < n :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h
    vec[off + j.val]))

/-- SAWCore `updSliceWithProof` — overwrite the window at `off` with
`ys`, bound kernel-checked as in `sliceWithProof_checkedM`. -/
def updSliceWithProof_checkedM (α : Type) (n off len : Nat)
    (xs : Except String (Vec n α)) (ys : Except String (Vec len α))
    (_h : off + len <= n) : Except String (Vec n α) := do
  let vec ← xs
  let ys' ← ys
  pure (Vector.ofFn (fun (j : Fin n) =>
    if hlo : off <= j.val then
      if hhi : j.val < off + len then
        have hidx : j.val - off < len := by omega
        ys'[j.val - off]
      else vec[j]
    else vec[j]))

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
  Vector.ofFnM (fun (i : Fin n) => v[i])

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

A reducible accessor for `Stream`'s index function. This is a regular
support-library operation for stream values, not a fix-shape lowering
target. Reducible so iota-reduction fires through it without a `simp`
call. -/

/-- SAWCore `streamGet` counterpart at the library level — project
the stream's index function and apply it (see the section comment). -/
@[reducible] def streamIdx (α : Type) : Stream α → Nat → α
  | Stream.MkStream f, i => f i

/-! ### Raw-position proof-carrying `fix` contract (post-R4)

The WRAPPED unique-fixed-point contract (`saw_fix_unique_exists` /
`saw_fix_choose`) is RETIRED: recognized wrapped fixes lower to
proven realizations (`saw_fix_bounded_choose`, `saw_stream_realize`)
and every other wrapped fix rejects with a named diagnostic — no
emitter may produce the retired names again (the driver harness's
obsolete-helper scan enforces this).

What remains is the RAW variant, covering raw result positions
(function-shaped values, proofs, indices), retained per Instance 3:
the obligation says the raw body has a unique fixed point, which
under SAW's `fix_unfold` forces the chosen witness to coincide with
the SAW value; if no unique fixed point exists the obligation is
unprovable. Believed corpus-unreachable for divergent shapes and
census-checked. -/
/-- The raw fix contract: `x` is a fixed point of `body` and every
fixed point equals `x` (see the section comment for why uniqueness
is the SAW link). -/
def saw_fix_unique_contract_raw.{u} (α : Sort u)
    (body : α → α) (x : α) : Prop :=
  body x = x ∧ ∀ y : α, body y = y → y = x

/-- The raw fix proof obligation: some `x` satisfies
`saw_fix_unique_contract_raw`. Emitted (and left to the prover) at
every raw-position `Prelude.fix`. -/
def saw_fix_unique_exists_raw.{u} (α : Sort u) (body : α → α) : Prop :=
  ∃ x : α, saw_fix_unique_contract_raw α body x

/-- The chosen unique fixed point — the emitted value of a
raw-position `Prelude.fix`, consuming the discharged obligation. -/
noncomputable def saw_fix_choose_raw.{u} (α : Sort u) (body : α → α)
    (h : saw_fix_unique_exists_raw α body) : α :=
  Classical.choose h

/-! ### Class F bounded-lookback `fix` realization (OP-3 successor)

`saw_fix_bounded n α d body` realizes a `Prelude.fix` at `Vec n α`
whose body the source-side recognizer (`classifyFixShape`,
SAWCoreLean.Term) has classified as a bounded-lookback recurrence
(Class F: element `i` of the output reads only elements `< i` of the
recursive input). It is the `n`-fold iteration of the UNTOUCHED
translated body from the pure placeholder seed
`Vector.replicate n d`. Nothing about the body is decomposed or
rebuilt, and the seed is DISCARDED: under the per-instance
productivity obligation `saw_fix_bounded_productive` (H_prod, proved
by unfolding the concrete body — never assumed), the result is
seed-independent, pure, and a fixed point of the body — see
`saw_fix_bounded_seed_irrelevant` / `saw_fix_bounded_pure` /
`saw_fix_bounded_fixed_point` in SAWCorePreludeProofs. The fixed-point
lemma is the SAW link: SAW's only spec for `fix` is `fix_unfold`, and
for a bounded-lookback body the stabilization lemma pins the
elementwise values uniquely, so the SAW value and this realization
coincide. Design + audit record:
doc/2026-07-15_op3-successor-design.md.

Emission (Slice R2) uses the noncomputable
`saw_fix_bounded_choose`, whose seed is drawn from the obligation's
own `Nonempty` witness — translated vector ELEMENTS are wrapped
(`Except String α`), so no raw placeholder `d : α` is generically
available at emission time (R2 amendment to the fourth-audit `d`
parameter; the placeholder moves INSIDE the proven obligation). The
computable `saw_fix_bounded` stays as the spec/self-test form; the
seed-irrelevance lemma exchanges the two. -/

/-- The `k`-th iterate of `body` from an arbitrary pure seed vector.
The general-seed form exists so the stabilization lemma can compare
iterates from DIFFERENT seeds (that is what makes the seed
discardable). -/
def saw_fix_bounded_iter_from (n : Nat) (α : Type) (s : Vec n α)
    (body : Except String (Vec n α) → Except String (Vec n α)) :
    Nat → Except String (Vec n α)
  | 0 => Pure.pure s
  | k + 1 => body (saw_fix_bounded_iter_from n α s body k)

/-- The `k`-th iterate from the replicated placeholder seed. -/
def saw_fix_bounded_iter (n : Nat) (α : Type) (d : α)
    (body : Except String (Vec n α) → Except String (Vec n α)) :
    Nat → Except String (Vec n α) :=
  saw_fix_bounded_iter_from n α (Vector.replicate n d) body

/-- `n`-fold iteration of the untouched translated fix body from a
pure placeholder seed. Element `i` stabilizes at iterate `i + 1`, so
`n` iterates fix every element of a `Vec n α`. -/
def saw_fix_bounded (n : Nat) (α : Type) (d : α)
    (body : Except String (Vec n α) → Except String (Vec n α)) :
    Except String (Vec n α) :=
  saw_fix_bounded_iter n α d body n

/-- H_prod: the per-instance productivity obligation for a Class-F
lowering. ALL fields are PROVEN per instance by unfolding the
concrete body (fourth-audit amendment A — element totality is part of
the obligation, not a trusted side condition):

* `seed` — the carrier is inhabited, so an iteration seed exists to
  be discarded (R2 amendment: the placeholder lives inside the
  obligation because translated vector elements are wrapped, so no
  raw `d : α` is available at emission time; trivial for `n = 0`
  via `⟨#v[]⟩` and for every concrete bitvector element type);
* `total` — the body maps every pure vector to a pure vector (its
  element computations neither manufacture errors on pure input nor
  drop them: if an element errored, the whole body application would,
  and `total` would be unprovable);
* `lookback` — element `i` of the output depends only on elements
  `< i` of a pure input (the semantic bounded-lookback fact; the
  recognizer's syntactic constant `-1` shift check is the gate, this
  is the proof). -/
structure saw_fix_bounded_productive (n : Nat) (α : Type)
    (body : Except String (Vec n α) → Except String (Vec n α)) :
    Prop where
  /-- The carrier is inhabited (see the structure docstring). -/
  seed : Nonempty (Vec n α)
  /-- The body maps every pure vector to a pure vector. -/
  total : ∀ v : Vec n α, ∃ w : Vec n α,
    body (Pure.pure v) = Pure.pure w
  /-- Output element `i` depends only on input elements `< i`. -/
  lookback : ∀ (v₁ v₂ w₁ w₂ : Vec n α),
    body (Pure.pure v₁) = Pure.pure w₁ →
    body (Pure.pure v₂) = Pure.pure w₂ →
    ∀ (i : Nat) (hi : i < n),
      (∀ (j : Nat) (hj : j < n), j < i → v₁[j] = v₂[j]) →
      w₁[i] = w₂[i]

/-- The emitted realization (Slice R2): `n`-fold iteration of the
untouched body from a seed drawn from the obligation's own `Nonempty`
witness. Noncomputable exactly like the retired `saw_fix_choose`;
`saw_fix_bounded_choose_eq_bounded` (SAWCorePreludeProofs) exchanges
it for the computable `saw_fix_bounded` at any placeholder, which is
how discharges actually compute. -/
noncomputable def saw_fix_bounded_choose (n : Nat) (α : Type)
    (body : Except String (Vec n α) → Except String (Vec n α))
    (h : saw_fix_bounded_productive n α body) :
    Except String (Vec n α) :=
  saw_fix_bounded_iter_from n α (Classical.choice h.seed) body n

/- Self-tests: a concrete -1-lookback recurrence
(`out[0] = 1, out[i] = in[i-1] + 1`) stabilizes to `[1, 2, 3]` in
`n = 3` iterations, from ANY seed (the placeholder is discarded), and
a body that errors propagates its OWN error string (never a
manufactured one). -/

/-- info: Except.ok { toArray := #[1, 2, 3], size_toArray := _ } -/
#guard_msgs in
#eval saw_fix_bounded 3 Nat 0 (fun rec => do
  let v ← rec
  Pure.pure #v[1, v[0] + 1, v[1] + 1])

/-- info: Except.ok { toArray := #[1, 2, 3], size_toArray := _ } -/
#guard_msgs in
#eval saw_fix_bounded 3 Nat 999 (fun rec => do
  let v ← rec
  Pure.pure #v[1, v[0] + 1, v[1] + 1])

/-- info: Except.error "boom" -/
#guard_msgs in
#eval saw_fix_bounded 2 Nat 0
  (fun _ => Except.error "boom" : Except String (Vec 2 Nat) →
    Except String (Vec 2 Nat))

/-! ### Class S-single stream `fix` realization (OP-3 successor, R3b)

A recognized single-step stream corecursion (`classifyStreamBody`,
SAWCoreLean.Term — identity read at the constant -1 shift from a
literal seed, fifth-audit amendment 1) is productive BY CONSTRUCTION:
its elements are pinned by index induction. `saw_stream_unfold`
realizes it as a total Lean stream; the per-instance obligation
`saw_stream_single_productive` (PROVEN at every emission site, never
assumed) carries the two facts the faithfulness argument needs:

* `faithful` — the VERBATIM Except-valued emitted element function,
  fed the realization back at `Pure.pure`, reproduces the
  realization elementwise (fifth-audit amendment 2: this equation is
  the SOLE loud-failure discriminator for streams — the totality
  analog is vacuous because `Stream` sits raw inside `Except`);
* `lookback` — the element function's value at index `i` depends
  only on the input stream's elements `< i` (the semantic -1-shift
  fact; enables the uniqueness theorem, fifth-audit amendment 3).

`saw_stream_unfold_unique` (SAWCorePreludeProofs) then pins ANY total
stream satisfying the elementwise equation to the realization — the
`fix_unfold` link, with no choice among fixed points: the emitted
value IS the realization. -/

/-- Total realization of a recognized single-step stream fix:
element `n` is the `n`-fold step from the seed. R3 emits it with
`step = fun prev => prev` (the identity read — the only validated
lowering); the general `step` instantiation is reserved for the
post-R4 iterate program. -/
def saw_stream_unfold (α : Type) (x0 : α) (step : α → α) : Stream α :=
  Stream.MkStream (fun n => Nat.rec x0 (fun _ prev => step prev) n)

/-- H_prod for streams: the per-instance PROVEN obligation for a
Class S-single lowering. See the section comment; both fields are
established by unfolding the concrete emitted element function. -/
structure saw_stream_single_productive (α : Type) (x0 : α)
    (step : α → α)
    (mkfn : Except String (Stream α) → Nat → Except String α) :
    Prop where
  /-- The verbatim emitted element function, fed the realization
  back, reproduces the realization elementwise — the sole
  loud-failure discriminator for streams (fifth-audit amendment 2). -/
  faithful : ∀ i : Nat,
    mkfn (Pure.pure (saw_stream_unfold α x0 step)) i =
      Pure.pure (streamIdx α (saw_stream_unfold α x0 step) i)
  /-- The element function's value at `i` depends only on stream
  elements at indices `< i`. -/
  lookback : ∀ (t₁ t₂ : Stream α) (i : Nat),
    (∀ j : Nat, j < i → streamIdx α t₁ j = streamIdx α t₂ j) →
    mkfn (Pure.pure t₁) i = mkfn (Pure.pure t₂) i

/-- The emitted realization for a recognized Class S-single fix: the
proof argument is consumed so an undischarged obligation is loud in
the audit tier, exactly like `atWithProof_checkedM`'s bounds. -/
def saw_stream_realize (α : Type) (x0 : α) (step : α → α)
    (mkfn : Except String (Stream α) → Nat → Except String α)
    (_h : saw_stream_single_productive α x0 step mkfn) :
    Except String (Stream α) :=
  Pure.pure (saw_stream_unfold α x0 step)

/-! ### Proof-carrying `MkStream` totality contract

SAW's `MkStream α f` produces a stream of raw `α` values. Under the
backend's value/error convention, a translated index function may instead
have type `Nat → Except String α`. The translator can lower such a function
to a raw stream only when Lean proves it is pointwise total: there is a raw
function `g` whose values exactly match the successful results of `f`. -/
/-- The `MkStream` totality obligation: the wrapped index function is
pointwise pure (see the section comment). Emitted, and left to the
prover, at every `MkStream` whose index function is wrapped. -/
def saw_mkStream_total_exists (α : Type)
    (f : Nat → Except String α) : Prop :=
  ∃ g : Nat → α, ∀ i : Nat, f i = Pure.pure (g i)

/-- The emitted `MkStream` lowering — builds the stream from the
proven-total function's raw witness, consuming the discharged
obligation. -/
noncomputable def saw_mkStream_choose (α : Type)
    (f : Nat → Except String α)
    (h : saw_mkStream_total_exists α f) : Except String (Stream α) :=
  Pure.pure (Stream.MkStream (Classical.choose h))

/-! ## Unsafe / transport primitives -/

/-- SAWCore's `coerce` transports a value across a type equality.
Phase 9 follow-up: this is just Lean's `cast`, not a soundness
gap — `Eq Type α β` is a real proof that types are equal, and
type-equality transport is admissible (it's literally an
identity function modulo the type label). The unsoundness
attached to coerce in practice comes from chaining it with
`unsafeAssert` to fabricate the required `Eq Type α β`; this
def doesn't introduce any new unsoundness beyond what
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

The principled approach: SAW's `unsafeAssert α x y` translates to an
**explicit proof obligation** @Eq α x y@ at the call site. The
emitted outline leaves a proof placeholder, and proof scripts may use
the Lean tactic @saw_unsafeAssert@ to attempt the discharge using only
sound tactics. When the tactic succeeds, the resulting proof term is a
genuine proof of the equality. When it fails, the user must either:

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

/-! ### `error` — the retired axiomatic models (historical note)

SAW declares `primitive error : (a : isort 1) → String → a`. Two
earlier models are RETIRED:

* `axiom error_unrestricted.{u} : (α : Sort (u+1)) → String → α`
  was *unsound* (from `error_unrestricted Empty "" : Empty` one
  derives `False`) and was deleted along with the user-facing
  `error.{u}` def.
* A blanket translation-time rejection of `Prelude.error` was the
  interim stance while the monadic emission landed.

The CURRENT model (Phase β + the 2026-07-14 audited raw-error
disposition): value-domain `error` translates to `saw_throw_error`
below — an ordinary `Except.error` rethrow of SAW's own message, no
axiom involved; function-typed `error` whose final result is
value-domain lowers to the constant-error function; raw-position
`error` (index/type/proof) REJECTS at translation with a named
diagnostic (see
`doc/2026-07-14_reachable-raw-error-disposition.md`). -/

/-! ## SAWCore error helper

The translator emits `saw_throw_error` for SAWCore's user-facing
`Prelude.error` keyword. It returns `Except String α`, so errors propagate
visibly through subsequent `Bind.bind` chains, matching Cryptol's semantics
that `error "msg"` is a real failure mode users should be able to reason
about. -/

/-- Wrapped 'Except.error' for SAWCore `error α msg` translation:
the message argument arrives wrapped (Phase β wraps any
SAWCore-value expression, including the @appendString …@ chain
that Cryptol uses to build error strings). Bind the message to
get a raw 'String', then construct the error. -/
@[reducible] def saw_throw_error (α : Type)
    (msg : Except String String) : Except String α :=
  Bind.bind msg Except.error

/- Self-tests: an ok message becomes the error VERBATIM (SAW's own
string, nothing interpolated), and an error inside the message
computation propagates ITSELF — the outer throw never masks it. -/

/-- info: Except.error "encountered call to error" -/
#guard_msgs in
#eval saw_throw_error Nat (Pure.pure "encountered call to error")

/-- info: Except.error "inner failure wins" -/
#guard_msgs in
#eval saw_throw_error Nat (Except.error "inner failure wins")

/-! ## SAW-Prelude string operations

SAW's `appendString`, `equalString`, and `bytesToString` come up
in real workflows because Cryptol's `error "msg"` desugars (via
`Cryptol.ecError`) to
`error α (appendString "encountered call to ..." (bytesToString len bytes))`
— so any Cryptol code that mentions `error "msg"` surfaces these
primitives after Cryptol→SAWCore elaboration. The `error` itself
routes to `saw_throw_error` (above), but its String argument is built
via these ops.

Audit (CG-4, 2026-05-07; wording refreshed 2026-07-14): pre-mapping
these primitives were catalogued as `reject` SpecialTreatments — any
Cryptol module using `error` would refuse to translate. With the
mappings here, Cryptol error-message strings translate cleanly and
flow into `saw_throw_error` as ordinary wrapped `String` values.
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
