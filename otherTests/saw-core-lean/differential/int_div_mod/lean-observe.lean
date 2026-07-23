import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: div_pp true"
      else "LEAN_OBSERVED: div_pp false"
  | Except.error _ => "LEAN_OBSERVED: div_pp error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: mod_pp true"
      else "LEAN_OBSERVED: mod_pp false"
  | Except.error _ => "LEAN_OBSERVED: mod_pp error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: div_np true"
      else "LEAN_OBSERVED: div_np false"
  | Except.error _ => "LEAN_OBSERVED: div_np error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: mod_np true"
      else "LEAN_OBSERVED: mod_np false"
  | Except.error _ => "LEAN_OBSERVED: mod_np error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: div_pn true"
      else "LEAN_OBSERVED: div_pn false"
  | Except.error _ => "LEAN_OBSERVED: div_pn error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: mod_pn true"
      else "LEAN_OBSERVED: mod_pn false"
  | Except.error _ => "LEAN_OBSERVED: mod_pn error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: div_nn true"
      else "LEAN_OBSERVED: div_nn false"
  | Except.error _ => "LEAN_OBSERVED: div_nn error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: mod_nn true"
      else "LEAN_OBSERVED: mod_nn false"
  | Except.error _ => "LEAN_OBSERVED: mod_nn error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: div_exact_np true"
      else "LEAN_OBSERVED: div_exact_np false"
  | Except.error _ => "LEAN_OBSERVED: div_exact_np error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: mod_exact_np true"
      else "LEAN_OBSERVED: mod_exact_np false"
  | Except.error _ => "LEAN_OBSERVED: mod_exact_np error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: div_by1_neg true"
      else "LEAN_OBSERVED: div_by1_neg false"
  | Except.error _ => "LEAN_OBSERVED: div_by1_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: div_0_neg true"
      else "LEAN_OBSERVED: div_0_neg false"
  | Except.error _ => "LEAN_OBSERVED: div_0_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: mod_0_neg true"
      else "LEAN_OBSERVED: mod_0_neg false"
  | Except.error _ => "LEAN_OBSERVED: mod_0_neg error"
