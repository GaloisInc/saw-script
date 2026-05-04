/-
Attack pattern: derive `False` via `error Empty "" : Empty` followed
by `Empty.elim`.

History: with the original `error.{u} : Sort (u+1) → String → α`
signature, this elaborated cleanly (Empty : Type 0 = Sort 1 fits
Sort (u+1) at u := 0), giving `False` from no hypothesis.

Fix: tightened to `error.{u} : (α : Type u) → [Inhabited α] →
String → α`. `Inhabited Empty` does not exist, so the call to
`error Empty "boom"` no longer synthesizes — and this attack is
blocked at instance synthesis. If this file ever elaborates clean,
soundness on the Lean side is broken.
-/

import CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePrimitives

theorem fake_false_via_empty : False := Empty.elim (error Empty "boom")
