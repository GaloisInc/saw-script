/-
Semantic discharge for the `record_update` driver's behavioral
claim: `(shift_y p dy).x == p.x` — a y-axis shift should not
disturb the x coordinate.

Why this proof exists separately from the driver: the SAW
specializer normalizes `(shift_y p dy).x` *before* emission, so
PointShift.shift_y_preserves_x lands in the .lean.good as
`bvEq 32 (proj_x p) (proj_x p)` — a tautology that doesn't
mention `shift_y` at all. Pinning that emission catches some
breakage classes (e.g. the property body emitting against the
wrong field) but does NOT catch a translator regression where
`shift_y` *itself* mis-translates such that calling `.x` on the
result gives a different value.

This proof closes that gap by reasoning about `PointShift.shift_y`
*directly*: we show that after applying `shift_y` to a point and
projecting `.x`, the result is the original `.x`, for arbitrary
inputs. If the translator silently emitted shift_y as also
overwriting x, this proof fails.

Test coverage audit (2026-05-07): added in response to
"`drivers/cryptol_module_record_update` is shape-only and would
pass even if shift_y silently overwrote x; recommend adding
`proofs/point_shift_property` discharging
`(shift_y p dy).x = p.x`."
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives

/-- The Lean type of a `Point = { x : [32], y : [32] }`. Mirrors
the shape SAW emits for a Cryptol record. -/
abbrev Point :=
  RecordType "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
    (RecordType "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
      EmptyType)

/-- The translator-emitted `.x` projection. `match` rather than
`RecordType.rec` so Lean's code generator is happy; the two are
definitionally equivalent (single-constructor inductive). -/
noncomputable def proj_x : Point → CryptolToLean.SAWCoreVectors.Vec 32 Bool
  | RecordType.RecordValue x _ => x

/-- y-shift preserves x: applying `PointShift.shift_y` and then
projecting `.x` returns the original `.x`. Proves the actual
semantic claim about shift_y, not the trivial post-normalization
emission of shift_y_preserves_x. Discharge: case on `p` (a
single-constructor inductive), unfold shift_y, and the nested
@RecordType.rec applications iota-reduce to `rfl`. -/
theorem shift_y_preserves_x_semantic
    (p : Point) (dy : CryptolToLean.SAWCoreVectors.Vec 32 Bool) :
    proj_x (PointShift.shift_y p dy) = proj_x p := by
  obtain ⟨px, prest⟩ := p
  unfold PointShift.shift_y proj_x
  rfl
