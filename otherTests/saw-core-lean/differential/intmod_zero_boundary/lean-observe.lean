import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: mod0_pos true"
      else "LEAN_OBSERVED: mod0_pos false"
  | Except.error _ => "LEAN_OBSERVED: mod0_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: mod0_neg true"
      else "LEAN_OBSERVED: mod0_neg false"
  | Except.error _ => "LEAN_OBSERVED: mod0_neg error"
