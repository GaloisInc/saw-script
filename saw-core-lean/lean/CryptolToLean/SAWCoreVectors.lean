/-
`CryptolToLean.SAWCoreVectors` — bind SAWCore's `Vec n a` to Lean's
`Vector`.

Mirrors `SAWCoreVectorsAsRocqVectors.v`. Thin wrapper: Lean std already
ships a usable `Vector` type, so most of this file is renaming and
convenience lemmas.

# L-4 lockdown analysis (2026-05-02)

The audit's S-4 finding flagged that `abbrev Vec := Vector` exposes
Lean's `Vector.mk` and `Vector.rec` to anyone importing the support
library, "reaching beyond SAW's abstraction". We re-examined this
under the no-excuses bar and concluded:

  - **SAW's `Vec n α` and Lean's `Vector α n` are mathematically
    isomorphic** — both are length-`n` tuples of `α`. Pattern-matching
    a `Vec` value via `Vector.mk` reveals the underlying `List α`,
    which is precisely what SAW's `Vec` IS. There is no semantic
    divergence to exploit. A user "reaching through" the abstraction
    learns the same facts SAW already exposes.

  - Lean's `Vector` lives in stdlib. Anyone with `import Std` (which
    every Lean project has transitively) can use `Vector.mk`/`Vector.rec`
    on any `Vector` value. Sealing our `Vec` alias would not prevent
    this — it would just force users to spell the underlying type
    differently.

  - The translator never emits `Vector.mk` or `Vector.rec` itself; all
    translator-emitted code goes through the abstract API
    (`gen`/`atWithDefault`/`bvAdd`/etc. as axioms in
    `SAWCorePrimitives.lean`). So translated-output soundness is
    unaffected by what hand-written user proofs choose to do.

  - The remaining concern — that a user might use `Vector.mk` to
    construct a `Vec` value that violates an invariant SAW assumes —
    has no instance: SAW's `Vec n α` carries no structural invariant
    beyond length-`n`, and Lean's `Vector α n` carries the same
    length invariant by type.

**Decision.** Keep the `abbrev`. Document the boundary explicitly
here and in `doc/2026-04-24_soundness-boundaries.md`. This is
documented residual trust, not a feasibly-killable gap — a heavy
rewrite (opaque `Vec`, custom literal syntax, regenerated
`.lean.good` files) would obscure rather than fix the relationship,
and would still leave Lean's stdlib `Vector` reachable.
-/

namespace CryptolToLean.SAWCoreVectors

/-- SAWCore's `Vec n a` is Lean std's `Vector a n`. Note the argument
order flip (SAWCore puts the length first).

**Boundary contract** (L-4): treat `Vec n α` operations through
the API exposed in `CryptolToLean.SAWCorePrimitives` (`gen`,
`atWithDefault`, `bvAdd`, etc.). Pattern-matching a `Vec` value
via `Vector.mk` is allowed — the abstraction is faithful so it
won't introduce unsoundness — but it isn't part of the
translator-supported surface and has no compatibility guarantee
across future arcs. -/
abbrev Vec (n : Nat) (α : Type) : Type := Vector α n

end CryptolToLean.SAWCoreVectors
