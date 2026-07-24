/- RECALIBRATED 2026-07-24 (V-H1): the surface this probe originally
   pinned was retired from the library; the row is now a DELETION PIN —
   see the .shouldfail.expected sidecar for the current contract. -/
/-
Probe pattern: derive `False` via `error Empty "..." : Empty`
followed by `Empty.elim`.

L-17 two-tier design (2026-05-04). The user-facing `error` is
constrained:
  def error.{u} (α : Type u) [Inhabited α] (_msg : String) : α := default

`Inhabited Empty` does not exist, so this probe fails at instance
synthesis.

(Translator-emitted code uses the unsafe `error_unrestricted`
axiom — that's still admissible at uninhabited types, faithful to
SAW. A user who *knowingly* writes `error_unrestricted` is
explicitly opting out of the safety guard; not silent unsoundness.)

If this file ever elaborates clean, the L-17 mitigation has been
inadvertently dropped — soundness drift.
-/

import CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePrimitives

theorem fake_false_via_empty : False := Empty.elim (error Empty "boom")
