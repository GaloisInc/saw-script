import Emitted
import CryptolToLean

open CryptolToLean.SAWCorePrimitives

#reduce match Observed (Num.TCNum 3) with
  | Except.error "sentinel" => "LEAN_OBSERVED: error: sentinel"
  | Except.error e => "LEAN_OBSERVED: wrong error: " ++ e
  | Except.ok true => "LEAN_OBSERVED: defaulted true"
  | Except.ok false => "LEAN_OBSERVED: defaulted false"
