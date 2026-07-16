import Emitted

-- sanctioned maxRecDepth (kernel recursion limit, not a tactic budget):
-- the realization's Classical.choice seed drops out of stabilized
-- elements under reduction, but the iterate tower is deep
set_option maxRecDepth 4096 in
#reduce match Observed with
  | Except.ok true => "LEAN_OBSERVED: true"
  | Except.ok false => "LEAN_OBSERVED: false"
  | Except.error e => "LEAN_OBSERVED: error: " ++ e
