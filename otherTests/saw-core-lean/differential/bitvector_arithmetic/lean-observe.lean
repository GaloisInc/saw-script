import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: add_plain true"
      else "LEAN_OBSERVED: add_plain false"
  | Except.error _ => "LEAN_OBSERVED: add_plain error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: add_wrap true"
      else "LEAN_OBSERVED: add_wrap false"
  | Except.error _ => "LEAN_OBSERVED: add_wrap error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: add_signflip true"
      else "LEAN_OBSERVED: add_signflip false"
  | Except.error _ => "LEAN_OBSERVED: add_signflip error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: sub_wrap true"
      else "LEAN_OBSERVED: sub_wrap false"
  | Except.error _ => "LEAN_OBSERVED: sub_wrap error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: sub_plain true"
      else "LEAN_OBSERVED: sub_plain false"
  | Except.error _ => "LEAN_OBSERVED: sub_plain error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: sub_self true"
      else "LEAN_OBSERVED: sub_self false"
  | Except.error _ => "LEAN_OBSERVED: sub_self error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: neg_minneg true"
      else "LEAN_OBSERVED: neg_minneg false"
  | Except.error _ => "LEAN_OBSERVED: neg_minneg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: neg_zero true"
      else "LEAN_OBSERVED: neg_zero false"
  | Except.error _ => "LEAN_OBSERVED: neg_zero error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: neg_one true"
      else "LEAN_OBSERVED: neg_one false"
  | Except.error _ => "LEAN_OBSERVED: neg_one error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: mul_wrap true"
      else "LEAN_OBSERVED: mul_wrap false"
  | Except.error _ => "LEAN_OBSERVED: mul_wrap error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: mul_msb true"
      else "LEAN_OBSERVED: mul_msb false"
  | Except.error _ => "LEAN_OBSERVED: mul_msb error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: mul_ffff true"
      else "LEAN_OBSERVED: mul_ffff false"
  | Except.error _ => "LEAN_OBSERVED: mul_ffff error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: mul_zero true"
      else "LEAN_OBSERVED: mul_zero false"
  | Except.error _ => "LEAN_OBSERVED: mul_zero error"

#reduce match Observed with
  | Except.ok v =>
      bif v[13]'(by decide) then "LEAN_OBSERVED: w1_add_wrap true"
      else "LEAN_OBSERVED: w1_add_wrap false"
  | Except.error _ => "LEAN_OBSERVED: w1_add_wrap error"

#reduce match Observed with
  | Except.ok v =>
      bif v[14]'(by decide) then "LEAN_OBSERVED: w1_neg true"
      else "LEAN_OBSERVED: w1_neg false"
  | Except.error _ => "LEAN_OBSERVED: w1_neg error"
