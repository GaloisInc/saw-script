import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_vector_zip was retired in the 2026-07-15 restructure; coverage lives in differential/).
-/

abbrev NatPair : Type := PairType Nat (PairType Nat UnitType)

def natPairDefault : NatPair :=
  PairType.PairValue 99 (PairType.PairValue 99 UnitType.Unit)

def zippedNatExample : Vec 2 NatPair :=
  zip Nat Nat 3 2 #v[1, 2, 3] #v[4, 5]

theorem zip_left_zero_semantics :
    Pair_fst Nat (PairType Nat UnitType)
      (atWithDefault 2 NatPair natPairDefault zippedNatExample 0) = 1 := by
  rfl

theorem zip_right_zero_semantics :
    Pair_fst Nat UnitType
      (Pair_snd Nat (PairType Nat UnitType)
        (atWithDefault 2 NatPair natPairDefault zippedNatExample 0)) = 4 := by
  rfl

theorem zip_left_one_semantics :
    Pair_fst Nat (PairType Nat UnitType)
      (atWithDefault 2 NatPair natPairDefault zippedNatExample 1) = 2 := by
  rfl

theorem zip_right_one_semantics :
    Pair_fst Nat UnitType
      (Pair_snd Nat (PairType Nat UnitType)
        (atWithDefault 2 NatPair natPairDefault zippedNatExample 1)) = 5 := by
  rfl

theorem zip_truncates_to_shorter_input :
    atWithDefault 2 NatPair natPairDefault zippedNatExample 2 = natPairDefault := by
  rfl

end
