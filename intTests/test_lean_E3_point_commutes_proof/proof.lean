/-
Stress-test E3 (tier 2): Point record-field commutativity.

Source: otherTests/saw-core-lean/test_offline_lean_stress.saw
Cryptol property:
    \(p1 p2 : Point) -> point_add p1 p2 == point_add p2 p1
where Point = { x : [32], y : [32] } and point_add adds fieldwise.

The emitted goal is a nested iteDep chain over bvEq of the x- and
y-field adds. Strategy:
  1. intro p1 p2
  2. cases each record down to RecordValue — RecordType.rec then
     reduces on these destructor matches.
  3. apply bvAdd_comm per field to flip the arguments.
  4. bvEq reflexivity closes each chain; iteDep collapses.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreBitvectorsProofs

noncomputable def goal : Prop :=
  (p1 : RecordType "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)) -> (p2 : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)) -> @Eq Bool
  (CryptolToLean.SAWCorePreludeExtra.ite Bool (bvEq 32 (bvAdd 32
  (@RecordType.rec "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) (fun (_ : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  EmptyType)) => CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) => x) p1)
  (@RecordType.rec "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) (fun (_ : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  EmptyType)) => CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) => x) p2)) (bvAdd 32
  (@RecordType.rec "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) (fun (_ : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  EmptyType)) => CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) => x) p2)
  (@RecordType.rec "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) (fun (_ : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  EmptyType)) => CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) => x) p1)))
  (CryptolToLean.SAWCorePreludeExtra.ite Bool (bvEq 32 (bvAdd 32
  (@RecordType.rec "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType
  (fun (_ : RecordType "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  EmptyType) => CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : EmptyType) => x)
  (@RecordType.rec "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) (fun (_ : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)) => RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) => y) p1))
  (@RecordType.rec "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType
  (fun (_ : RecordType "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  EmptyType) => CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : EmptyType) => x)
  (@RecordType.rec "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) (fun (_ : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)) => RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) => y) p2))) (bvAdd 32
  (@RecordType.rec "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType
  (fun (_ : RecordType "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  EmptyType) => CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : EmptyType) => x)
  (@RecordType.rec "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) (fun (_ : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)) => RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) => y) p2))
  (@RecordType.rec "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType
  (fun (_ : RecordType "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  EmptyType) => CryptolToLean.SAWCoreVectors.Vec 32 Bool)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : EmptyType) => x)
  (@RecordType.rec "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType
  "y" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) (fun (_ : RecordType
  "x" (CryptolToLean.SAWCoreVectors.Vec 32 Bool) (RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)) => RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType)
  (fun (x : CryptolToLean.SAWCoreVectors.Vec 32 Bool) (y : RecordType "y"
  (CryptolToLean.SAWCoreVectors.Vec 32 Bool) EmptyType) => y) p1)))) Bool.true
  Bool.false) Bool.false) Bool.true

theorem goal_holds : goal := by
  intro p1 p2
  obtain ⟨p1x, p1y⟩ := p1
  obtain ⟨p2x, p2y⟩ := p2
  -- After destructuring, RecordType.rec applications reduce to
  -- the field values directly.
  -- Rewrite both commuted halves to match their already-symmetric
  -- counterparts, then the remaining ite chain collapses.
  rw [bvAdd_comm 32 p1x p2x, bvAdd_comm 32 p1y.1 p2y.1]
  simp [bvEq_refl]
