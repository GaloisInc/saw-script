import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCoreVectors

noncomputable def sample : RecordType "x" (Vec 8 Bool) (RecordType "y" (Vec 8 Bool) EmptyType) :=
  @RecordType.RecordValue "x" (Vec 8 Bool) (RecordType "y" (Vec 8 Bool) EmptyType)
    (bvNat 8 42)
    (@RecordType.RecordValue "y" (Vec 8 Bool) EmptyType
      (bvNat 8 100)
      EmptyType.Empty)

#reduce match Observed (Pure.pure sample) with
  | Except.ok v =>
      if bvEq 8 v (bvNat 8 42) then
        "LEAN_OBSERVED: true"
      else
        "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
