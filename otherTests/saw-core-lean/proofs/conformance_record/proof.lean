import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
Lean half of `drivers/conformance_record`.

The SAW driver proves concrete Cryptol record facts with SAW's `w4` backend
and emits the same source property for Lean elaboration. This file pins the
corresponding `RecordType` support-library realization directly.
-/

abbrev bv8 (n : Nat) : Vec 8 Bool := bvNat 8 n

abbrev Point : Type :=
  RecordType "x" (Vec 8 Bool)
    (RecordType "y" (Vec 8 Bool) EmptyType)

abbrev NestedPoint : Type :=
  RecordType "inner" Point
    (RecordType "z" (Vec 8 Bool) EmptyType)

def point12 : Point :=
  RecordType.RecordValue (bv8 1)
    (RecordType.RecordValue (bv8 2) EmptyType.Empty)

def point32 : Point :=
  RecordType.RecordValue (bv8 3)
    (RecordType.RecordValue (bv8 2) EmptyType.Empty)

def point17 : Point :=
  RecordType.RecordValue (bv8 1)
    (RecordType.RecordValue (bvAdd 8 (bv8 2) (bv8 5)) EmptyType.Empty)

def nestedPoint : NestedPoint :=
  RecordType.RecordValue point12
    (RecordType.RecordValue (bv8 3) EmptyType.Empty)

theorem record_x_projection_semantics :
    (match point12 with
     | RecordType.RecordValue x _ => x) = bv8 1 := by
  rfl

theorem record_y_projection_semantics :
    (match (match point12 with
            | RecordType.RecordValue _ rest => rest) with
     | RecordType.RecordValue y _ => y) = bv8 2 := by
  rfl

theorem nested_record_projection_semantics :
    (match (match nestedPoint with
            | RecordType.RecordValue inner _ => inner) with
     | RecordType.RecordValue x _ => x) = bv8 1 := by
  rfl

theorem record_update_x_semantics :
    (match point32 with
     | RecordType.RecordValue x _ => x) = bv8 3 := by
  rfl

theorem record_relative_update_y_semantics :
    (match (match point17 with
            | RecordType.RecordValue _ rest => rest) with
     | RecordType.RecordValue y _ => y) = bv8 7 := by
  decide

end
