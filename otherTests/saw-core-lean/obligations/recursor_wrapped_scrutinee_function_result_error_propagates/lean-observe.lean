import Emitted

#reduce match Observed (Except.error "sentinel") (Pure.pure true) with
  | Except.error "sentinel" => "LEAN_OBSERVED: error: sentinel"
  | Except.error e => "LEAN_OBSERVED: wrong error: " ++ e
  | Except.ok true => "LEAN_OBSERVED: defaulted true"
  | Except.ok false => "LEAN_OBSERVED: defaulted false"
