/-
Discharge proof for test_offline_lean.t4_prove0.

Cryptol property: \(b : Bit) (x : [8]) (y : [8]) ->
                    (if b then x else y) == (if ~b then y else x).

Pure Bool case-symmetry: case-split on b, both sides reduce.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro b x y
  unfold CryptolToLean.SAWCorePreludeExtra.ite
  cases b
  · exact bvEq_refl 8 _
  · exact bvEq_refl 8 _
