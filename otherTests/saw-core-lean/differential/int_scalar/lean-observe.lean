import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: add_mixed true"
      else "LEAN_OBSERVED: add_mixed false"
  | Except.error _ => "LEAN_OBSERVED: add_mixed error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: sub_cross true"
      else "LEAN_OBSERVED: sub_cross false"
  | Except.error _ => "LEAN_OBSERVED: sub_cross error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: mul_neg true"
      else "LEAN_OBSERVED: mul_neg false"
  | Except.error _ => "LEAN_OBSERVED: mul_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: mul_negneg true"
      else "LEAN_OBSERVED: mul_negneg false"
  | Except.error _ => "LEAN_OBSERVED: mul_negneg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: le_neg true"
      else "LEAN_OBSERVED: le_neg false"
  | Except.error _ => "LEAN_OBSERVED: le_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: lt_neg true"
      else "LEAN_OBSERVED: lt_neg false"
  | Except.error _ => "LEAN_OBSERVED: lt_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: le_refl true"
      else "LEAN_OBSERVED: le_refl false"
  | Except.error _ => "LEAN_OBSERVED: le_refl error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: lt_irrefl true"
      else "LEAN_OBSERVED: lt_irrefl false"
  | Except.error _ => "LEAN_OBSERVED: lt_irrefl error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: neg_zero true"
      else "LEAN_OBSERVED: neg_zero false"
  | Except.error _ => "LEAN_OBSERVED: neg_zero error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: abs_neg true"
      else "LEAN_OBSERVED: abs_neg false"
  | Except.error _ => "LEAN_OBSERVED: abs_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: abs_pos true"
      else "LEAN_OBSERVED: abs_pos false"
  | Except.error _ => "LEAN_OBSERVED: abs_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: abs_zero true"
      else "LEAN_OBSERVED: abs_zero false"
  | Except.error _ => "LEAN_OBSERVED: abs_zero error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: min_mixed true"
      else "LEAN_OBSERVED: min_mixed false"
  | Except.error _ => "LEAN_OBSERVED: min_mixed error"

#reduce match Observed with
  | Except.ok v =>
      bif v[13]'(by decide) then "LEAN_OBSERVED: max_mixed true"
      else "LEAN_OBSERVED: max_mixed false"
  | Except.error _ => "LEAN_OBSERVED: max_mixed error"

#reduce match Observed with
  | Except.ok v =>
      bif v[14]'(by decide) then "LEAN_OBSERVED: min_negneg true"
      else "LEAN_OBSERVED: min_negneg false"
  | Except.error _ => "LEAN_OBSERVED: min_negneg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[15]'(by decide) then "LEAN_OBSERVED: toNat_neg true"
      else "LEAN_OBSERVED: toNat_neg false"
  | Except.error _ => "LEAN_OBSERVED: toNat_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[16]'(by decide) then "LEAN_OBSERVED: toNat_pos true"
      else "LEAN_OBSERVED: toNat_pos false"
  | Except.error _ => "LEAN_OBSERVED: toNat_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[17]'(by decide) then "LEAN_OBSERVED: toNat_zero true"
      else "LEAN_OBSERVED: toNat_zero false"
  | Except.error _ => "LEAN_OBSERVED: toNat_zero error"
