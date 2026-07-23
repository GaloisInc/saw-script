import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: bvToNat_ff true"
      else "LEAN_OBSERVED: bvToNat_ff false"
  | Except.error _ => "LEAN_OBSERVED: bvToNat_ff error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: bvToNat_00 true"
      else "LEAN_OBSERVED: bvToNat_00 false"
  | Except.error _ => "LEAN_OBSERVED: bvToNat_00 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: bvToNat_w1 true"
      else "LEAN_OBSERVED: bvToNat_w1 false"
  | Except.error _ => "LEAN_OBSERVED: bvToNat_w1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: bvToInt_7f true"
      else "LEAN_OBSERVED: bvToInt_7f false"
  | Except.error _ => "LEAN_OBSERVED: bvToInt_7f error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: bvToInt_80 true"
      else "LEAN_OBSERVED: bvToInt_80 false"
  | Except.error _ => "LEAN_OBSERVED: bvToInt_80 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: bvToInt_ff true"
      else "LEAN_OBSERVED: bvToInt_ff false"
  | Except.error _ => "LEAN_OBSERVED: bvToInt_ff error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: bvToInt_00 true"
      else "LEAN_OBSERVED: bvToInt_00 false"
  | Except.error _ => "LEAN_OBSERVED: bvToInt_00 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: bvToInt_w1_1 true"
      else "LEAN_OBSERVED: bvToInt_w1_1 false"
  | Except.error _ => "LEAN_OBSERVED: bvToInt_w1_1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: sbvToInt_7f true"
      else "LEAN_OBSERVED: sbvToInt_7f false"
  | Except.error _ => "LEAN_OBSERVED: sbvToInt_7f error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: sbvToInt_80 true"
      else "LEAN_OBSERVED: sbvToInt_80 false"
  | Except.error _ => "LEAN_OBSERVED: sbvToInt_80 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: sbvToInt_ff true"
      else "LEAN_OBSERVED: sbvToInt_ff false"
  | Except.error _ => "LEAN_OBSERVED: sbvToInt_ff error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: sbvToInt_w1_1 true"
      else "LEAN_OBSERVED: sbvToInt_w1_1 false"
  | Except.error _ => "LEAN_OBSERVED: sbvToInt_w1_1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: sbvToInt_w1_0 true"
      else "LEAN_OBSERVED: sbvToInt_w1_0 false"
  | Except.error _ => "LEAN_OBSERVED: sbvToInt_w1_0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[13]'(by decide) then "LEAN_OBSERVED: to_int_agree_pos true"
      else "LEAN_OBSERVED: to_int_agree_pos false"
  | Except.error _ => "LEAN_OBSERVED: to_int_agree_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[14]'(by decide) then "LEAN_OBSERVED: bvNat_max true"
      else "LEAN_OBSERVED: bvNat_max false"
  | Except.error _ => "LEAN_OBSERVED: bvNat_max error"

#reduce match Observed with
  | Except.ok v =>
      bif v[15]'(by decide) then "LEAN_OBSERVED: bvNat_wrap_256 true"
      else "LEAN_OBSERVED: bvNat_wrap_256 false"
  | Except.error _ => "LEAN_OBSERVED: bvNat_wrap_256 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[16]'(by decide) then "LEAN_OBSERVED: bvNat_wrap_257 true"
      else "LEAN_OBSERVED: bvNat_wrap_257 false"
  | Except.error _ => "LEAN_OBSERVED: bvNat_wrap_257 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[17]'(by decide) then "LEAN_OBSERVED: intToBv_neg1 true"
      else "LEAN_OBSERVED: intToBv_neg1 false"
  | Except.error _ => "LEAN_OBSERVED: intToBv_neg1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[18]'(by decide) then "LEAN_OBSERVED: intToBv_neg128 true"
      else "LEAN_OBSERVED: intToBv_neg128 false"
  | Except.error _ => "LEAN_OBSERVED: intToBv_neg128 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[19]'(by decide) then "LEAN_OBSERVED: intToBv_neg129 true"
      else "LEAN_OBSERVED: intToBv_neg129 false"
  | Except.error _ => "LEAN_OBSERVED: intToBv_neg129 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[20]'(by decide) then "LEAN_OBSERVED: intToBv_257 true"
      else "LEAN_OBSERVED: intToBv_257 false"
  | Except.error _ => "LEAN_OBSERVED: intToBv_257 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[21]'(by decide) then "LEAN_OBSERVED: intToBv_neg256 true"
      else "LEAN_OBSERVED: intToBv_neg256 false"
  | Except.error _ => "LEAN_OBSERVED: intToBv_neg256 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[22]'(by decide) then "LEAN_OBSERVED: rt_unsigned true"
      else "LEAN_OBSERVED: rt_unsigned false"
  | Except.error _ => "LEAN_OBSERVED: rt_unsigned error"

#reduce match Observed with
  | Except.ok v =>
      bif v[23]'(by decide) then "LEAN_OBSERVED: rt_signed true"
      else "LEAN_OBSERVED: rt_signed false"
  | Except.error _ => "LEAN_OBSERVED: rt_signed error"
