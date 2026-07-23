import Emitted

open CryptolToLean.SAWCorePrimitives

#reduce match Observed with
  | Except.ok (m, e) =>
      bif m == 6 && e == 7 then "LEAN_OBSERVED: mkDouble pair 6 7"
      else "LEAN_OBSERVED: wrong pair"
  | Except.error err => "LEAN_OBSERVED: error: " ++ err
