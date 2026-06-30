/-
Stress-test E3 (tier 2): Point record-field commutativity.

Source: otherTests/saw-core-lean/test_offline_lean_stress.E3_prove0.lean
Cryptol property:
    \(p1 p2 : Point) -> point_add p1 p2 == point_add p2 p1
where Point = { x : [32], y : [32] }.

After destructuring both records with `obtain`, the
RecordType.rec projections reduce, bvAdd_comm flips each field,
and simp [bvEq_refl] collapses the final ite chain.
-/

import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

theorem goal_closed : goal := by
  intro p1 p2
  obtain ⟨p1x, p1y⟩ := p1
  obtain ⟨p2x, p2y⟩ := p2
  simp [CryptolToLean.SAWCorePreludeExtra.iteM, bvAdd_comm, bvEq_refl,
    Pure.pure, Bind.bind, Except.pure, Except.bind]
