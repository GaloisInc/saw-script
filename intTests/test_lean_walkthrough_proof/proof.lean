/-
Worked example for `doc/getting-started.md`. Pin both that the
saw-core-lean output for Cryptol's pure-Bool distributivity
(`(a && b) || (a && c) == a && (b || c)`) elaborates AND that a
short tactic proof discharges the goal.

If this file ever fails to compile, the getting-started doc's
worked example is broken — a guide to discharge that doesn't
actually discharge would mislead users.
-/

import CryptolToLean
open CryptolToLean.SAWCorePrimitives

-- Goal: literal copy of test_offline_lean.t2_prove0.lean.good's
-- emitted Prop. Cryptol source:
--   \(a : Bit) (b : Bit) (c : Bit) ->
--     (a && b) || (a && c) == a && (b || c)
noncomputable def goal : Prop :=
  (a : Bool) -> (b : Bool) -> (c : Bool) -> @Eq Bool
    (CryptolToLean.SAWCorePreludeExtra.ite Bool
       (CryptolToLean.SAWCorePreludeExtra.ite Bool
          (CryptolToLean.SAWCorePreludeExtra.ite Bool a b Bool.false)
          Bool.true
          (CryptolToLean.SAWCorePreludeExtra.ite Bool a c Bool.false))
       (CryptolToLean.SAWCorePreludeExtra.ite Bool a
          (CryptolToLean.SAWCorePreludeExtra.ite Bool b Bool.true c)
          Bool.false)
       (CryptolToLean.SAWCorePreludeExtra.ite Bool
          (CryptolToLean.SAWCorePreludeExtra.ite Bool a
             (CryptolToLean.SAWCorePreludeExtra.ite Bool b Bool.true c)
             Bool.false) Bool.false
          Bool.true)) Bool.true

-- Discharge: the iteDep/ite wrappers in SAWCorePreludeExtra are
-- '@[reducible]', so applied to concrete Bool args they reduce
-- definitionally. Eight cases (2^3 over a, b, c), each definitionally
-- 'rfl'.
theorem goal_holds : goal := by
  intro a b c
  cases a <;> cases b <;> cases c <;> rfl
