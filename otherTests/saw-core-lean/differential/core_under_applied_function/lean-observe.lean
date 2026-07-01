import Emitted

#reduce match Observed (Except.ok false) with
  | Except.ok true => "LEAN_OBSERVED: true"
  | Except.ok false => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
