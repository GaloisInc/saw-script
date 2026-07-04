import Emitted

#reduce match Observed (Except.error "sentinel") with
  | Except.error "sentinel" => "LEAN_OBSERVED: error: sentinel"
  | Except.error e => "LEAN_OBSERVED: wrong error: " ++ e
  | Except.ok _ => "LEAN_OBSERVED: defaulted"
