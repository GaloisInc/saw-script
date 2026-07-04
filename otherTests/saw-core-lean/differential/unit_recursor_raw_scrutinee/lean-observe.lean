import Emitted

#reduce match Observed (Pure.pure CryptolToLean.SAWCorePrimitives.UnitType.Unit) with
  | Except.ok 7 => "LEAN_OBSERVED: true"
  | Except.ok _ => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
