/-
Attack pattern: derive `False` via `error Empty "..." : Empty`
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
