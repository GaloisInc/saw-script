import Emitted

/- Apply the emitted OPEN function at the same concrete arguments SAW
evaluated: a = -3 (negative operand), b = 5. -/
#reduce match Observed (Pure.pure (-3 : Int)) (Pure.pure (5 : Int)) with
  | Except.ok true => "LEAN_OBSERVED: true"
  | Except.ok false => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
