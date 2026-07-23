import Emitted

open CryptolToLean.SAWCorePrimitives

#reduce match Observed with
  | Except.ok (m, e) =>
      bif m == 1 && e == 2 then "LEAN_OBSERVED: mkFloat pair 1 2"
      else "LEAN_OBSERVED: wrong pair"
  | Except.error err => "LEAN_OBSERVED: error: " ++ err
