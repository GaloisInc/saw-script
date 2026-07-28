import Emitted

-- Pairwise labeled observer for the LIB-1 lazy-vector litmus.
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.
--
-- Expected divergence (this row is a pinned known gap): SAW
-- observes true/true/false; the collapsed carrier makes every
-- case Except.error "e", so Lean observes error/error/error.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: lazy_elem_A_eq_7 true"
      else "LEAN_OBSERVED: lazy_elem_A_eq_7 false"
  | Except.error _ => "LEAN_OBSERVED: lazy_elem_A_eq_7 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: lazy_elem_B_eq_9 true"
      else "LEAN_OBSERVED: lazy_elem_B_eq_9 false"
  | Except.error _ => "LEAN_OBSERVED: lazy_elem_B_eq_9 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: lazy_A_eq_B true"
      else "LEAN_OBSERVED: lazy_A_eq_B false"
  | Except.error _ => "LEAN_OBSERVED: lazy_A_eq_B error"
