import Emitted
import CryptolToLean

#reduce match Observed
    (CryptolToLean.SAWCorePrimitives.Num.TCNum 2)
    (Pure.pure (CryptolToLean.SAWCorePrimitives.gen 2
      (CryptolToLean.SAWCoreVectors.Vec 4 Bool)
      (fun _ => CryptolToLean.SAWCorePrimitives.bvNat 4 10))) with
  | Except.ok true => "LEAN_OBSERVED: true"
  | Except.ok false => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
