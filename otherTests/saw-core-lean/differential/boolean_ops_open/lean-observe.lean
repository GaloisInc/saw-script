import Emitted

/- Apply the emitted OPEN function at the same concrete arguments SAW
evaluated: a = True, b = False. -/
#reduce match Observed (Pure.pure Bool.true) (Pure.pure Bool.false) with
  | Except.ok true => "LEAN_OBSERVED: true"
  | Except.ok false => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
