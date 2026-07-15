import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_tuple was retired in the 2026-07-15 restructure; coverage lives in differential/).

The SAW driver proves concrete tuple projection facts with SAW's `w4` backend
and emits the same source property for Lean elaboration. This file pins the
corresponding `PairType` support-library realization directly.
-/

abbrev bv8 (n : Nat) : Vec 8 Bool := bvNat 8 n

theorem pair_fst_semantics :
    Pair_fst (Vec 8 Bool) (PairType (Vec 8 Bool) UnitType)
      (PairType.PairValue (bv8 1)
        (PairType.PairValue (bv8 2) UnitType.Unit)) = bv8 1 := by
  rfl

theorem pair_snd_semantics :
    Pair_fst (Vec 8 Bool) UnitType
      (Pair_snd (Vec 8 Bool) (PairType (Vec 8 Bool) UnitType)
        (PairType.PairValue (bv8 1)
          (PairType.PairValue (bv8 2) UnitType.Unit))) = bv8 2 := by
  rfl

theorem nested_pair_fst_snd_semantics :
    Pair_fst (Vec 8 Bool) UnitType
      (Pair_snd (Vec 8 Bool) (PairType (Vec 8 Bool) UnitType)
        (Pair_fst
          (PairType (Vec 8 Bool) (PairType (Vec 8 Bool) UnitType))
          (PairType (Vec 8 Bool) UnitType)
          (PairType.PairValue
            (PairType.PairValue (bv8 1)
              (PairType.PairValue (bv8 2) UnitType.Unit))
            (PairType.PairValue (bv8 3) UnitType.Unit)))) = bv8 2 := by
  rfl

theorem nested_pair_snd_semantics :
    Pair_fst (Vec 8 Bool) UnitType
      (Pair_snd
        (PairType (Vec 8 Bool) (PairType (Vec 8 Bool) UnitType))
        (PairType (Vec 8 Bool) UnitType)
        (PairType.PairValue
          (PairType.PairValue (bv8 1)
            (PairType.PairValue (bv8 2) UnitType.Unit))
          (PairType.PairValue (bv8 3) UnitType.Unit))) = bv8 3 := by
  rfl

end
