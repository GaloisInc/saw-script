/-
Discharge for test_cryptol_zn_arith.addcomm_prove0 (workflow row
workflows/cryptol_zn_arith).

Cryptol property: \(x : Z 7) (y : Z 7) -> x + y == y + x.

The IntMod `Z 7` values are `Int`; `intModAdd 7 a b = Int.fmod (a+b) 7`
and `intModEq 7` compares under `Int.fmod`. Since `a + b = b + a` in
`Int` (Int.add_comm), the two sides are literally equal and the
`decide` collapses to `True`.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives

theorem goal_closed : goal := by
  intro x y
  simp only [Pure.pure, Bind.bind, Except.pure, Except.bind]
  simp only [intModEq, intModAdd, Int.add_comm, decide_true]
