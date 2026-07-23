import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: add true"
      else "LEAN_OBSERVED: add false"
  | Except.error _ => "LEAN_OBSERVED: add error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: pred_zero true"
      else "LEAN_OBSERVED: pred_zero false"
  | Except.error _ => "LEAN_OBSERVED: pred_zero error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: pred_one true"
      else "LEAN_OBSERVED: pred_one false"
  | Except.error _ => "LEAN_OBSERVED: pred_one error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: lt true"
      else "LEAN_OBSERVED: lt false"
  | Except.error _ => "LEAN_OBSERVED: lt error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: lt_irrefl true"
      else "LEAN_OBSERVED: lt_irrefl false"
  | Except.error _ => "LEAN_OBSERVED: lt_irrefl error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: sub_saturate true"
      else "LEAN_OBSERVED: sub_saturate false"
  | Except.error _ => "LEAN_OBSERVED: sub_saturate error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: sub_exact true"
      else "LEAN_OBSERVED: sub_exact false"
  | Except.error _ => "LEAN_OBSERVED: sub_exact error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: sub_plain true"
      else "LEAN_OBSERVED: sub_plain false"
  | Except.error _ => "LEAN_OBSERVED: sub_plain error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: mul_zero true"
      else "LEAN_OBSERVED: mul_zero false"
  | Except.error _ => "LEAN_OBSERVED: mul_zero error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: mul_plain true"
      else "LEAN_OBSERVED: mul_plain false"
  | Except.error _ => "LEAN_OBSERVED: mul_plain error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: double true"
      else "LEAN_OBSERVED: double false"
  | Except.error _ => "LEAN_OBSERVED: double error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: exp_0_0 true"
      else "LEAN_OBSERVED: exp_0_0 false"
  | Except.error _ => "LEAN_OBSERVED: exp_0_0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: exp_0_3 true"
      else "LEAN_OBSERVED: exp_0_3 false"
  | Except.error _ => "LEAN_OBSERVED: exp_0_3 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[13]'(by decide) then "LEAN_OBSERVED: exp_5_0 true"
      else "LEAN_OBSERVED: exp_5_0 false"
  | Except.error _ => "LEAN_OBSERVED: exp_5_0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[14]'(by decide) then "LEAN_OBSERVED: exp_2_10 true"
      else "LEAN_OBSERVED: exp_2_10 false"
  | Except.error _ => "LEAN_OBSERVED: exp_2_10 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[15]'(by decide) then "LEAN_OBSERVED: min_lo true"
      else "LEAN_OBSERVED: min_lo false"
  | Except.error _ => "LEAN_OBSERVED: min_lo error"

#reduce match Observed with
  | Except.ok v =>
      bif v[16]'(by decide) then "LEAN_OBSERVED: min_eq true"
      else "LEAN_OBSERVED: min_eq false"
  | Except.error _ => "LEAN_OBSERVED: min_eq error"

#reduce match Observed with
  | Except.ok v =>
      bif v[17]'(by decide) then "LEAN_OBSERVED: max_hi true"
      else "LEAN_OBSERVED: max_hi false"
  | Except.error _ => "LEAN_OBSERVED: max_hi error"

#reduce match Observed with
  | Except.ok v =>
      bif v[18]'(by decide) then "LEAN_OBSERVED: div_basic true"
      else "LEAN_OBSERVED: div_basic false"
  | Except.error _ => "LEAN_OBSERVED: div_basic error"

#reduce match Observed with
  | Except.ok v =>
      bif v[19]'(by decide) then "LEAN_OBSERVED: mod_basic true"
      else "LEAN_OBSERVED: mod_basic false"
  | Except.error _ => "LEAN_OBSERVED: mod_basic error"

#reduce match Observed with
  | Except.ok v =>
      bif v[20]'(by decide) then "LEAN_OBSERVED: div_by1 true"
      else "LEAN_OBSERVED: div_by1 false"
  | Except.error _ => "LEAN_OBSERVED: div_by1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[21]'(by decide) then "LEAN_OBSERVED: div_0_x true"
      else "LEAN_OBSERVED: div_0_x false"
  | Except.error _ => "LEAN_OBSERVED: div_0_x error"

#reduce match Observed with
  | Except.ok v =>
      bif v[22]'(by decide) then "LEAN_OBSERVED: mod_exact true"
      else "LEAN_OBSERVED: mod_exact false"
  | Except.error _ => "LEAN_OBSERVED: mod_exact error"

#reduce match Observed with
  | Except.ok v =>
      bif v[23]'(by decide) then "LEAN_OBSERVED: if0_zero true"
      else "LEAN_OBSERVED: if0_zero false"
  | Except.error _ => "LEAN_OBSERVED: if0_zero error"

#reduce match Observed with
  | Except.ok v =>
      bif v[24]'(by decide) then "LEAN_OBSERVED: if0_succ true"
      else "LEAN_OBSERVED: if0_succ false"
  | Except.error _ => "LEAN_OBSERVED: if0_succ error"
