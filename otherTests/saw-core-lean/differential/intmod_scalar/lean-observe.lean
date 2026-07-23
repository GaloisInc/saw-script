import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: from_to true"
      else "LEAN_OBSERVED: from_to false"
  | Except.error _ => "LEAN_OBSERVED: from_to error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: sub_wrap true"
      else "LEAN_OBSERVED: sub_wrap false"
  | Except.error _ => "LEAN_OBSERVED: sub_wrap error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: mul_wrap true"
      else "LEAN_OBSERVED: mul_wrap false"
  | Except.error _ => "LEAN_OBSERVED: mul_wrap error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: neg_rep true"
      else "LEAN_OBSERVED: neg_rep false"
  | Except.error _ => "LEAN_OBSERVED: neg_rep error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: neg_rep_big true"
      else "LEAN_OBSERVED: neg_rep_big false"
  | Except.error _ => "LEAN_OBSERVED: neg_rep_big error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: eq_noncanon true"
      else "LEAN_OBSERVED: eq_noncanon false"
  | Except.error _ => "LEAN_OBSERVED: eq_noncanon error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: eq_neg_pos true"
      else "LEAN_OBSERVED: eq_neg_pos false"
  | Except.error _ => "LEAN_OBSERVED: eq_neg_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: add_wrap true"
      else "LEAN_OBSERVED: add_wrap false"
  | Except.error _ => "LEAN_OBSERVED: add_wrap error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: neg_op true"
      else "LEAN_OBSERVED: neg_op false"
  | Except.error _ => "LEAN_OBSERVED: neg_op error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: neg_op_zero true"
      else "LEAN_OBSERVED: neg_op_zero false"
  | Except.error _ => "LEAN_OBSERVED: neg_op_zero error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: mod1_seven true"
      else "LEAN_OBSERVED: mod1_seven false"
  | Except.error _ => "LEAN_OBSERVED: mod1_seven error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: mod1_eq true"
      else "LEAN_OBSERVED: mod1_eq false"
  | Except.error _ => "LEAN_OBSERVED: mod1_eq error"
