/-
Worked example for `doc/getting-started.md`. Discharge the
emitted Cryptol pure-Bool distributivity goal:

    \(a : Bit) (b : Bit) (c : Bit) ->
      (a && b) || (a && c) == a && (b || c)

If this proof ever breaks, the getting-started doc's worked
example is misleading users.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives

-- The iteDep / ite wrappers in SAWCorePreludeExtra are @[reducible],
-- so applied to concrete Bool args they reduce definitionally. Eight
-- cases (2³ over a, b, c), each closed by rfl.
theorem goal_closed : goal := by
  intro a b c
  cases a <;> cases b <;> cases c <;> rfl
