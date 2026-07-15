/-
t7: implication chain over Bit — (a ==> b) && (b ==> c) ==> (a ==> c).

Source: workflows/offline_lean/test_offline_lean.t7_prove0.lean

Finite Bool property emitted as nested `iteM` over pure booleans;
case split on all three variables and reduce (the walkthrough pattern).
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives

theorem goal_closed : goal := by
  intro a b c
  cases a <;> cases b <;> cases c <;> rfl
