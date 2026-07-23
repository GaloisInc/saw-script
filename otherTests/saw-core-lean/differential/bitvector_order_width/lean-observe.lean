import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: ult_basic true"
      else "LEAN_OBSERVED: ult_basic false"
  | Except.error _ => "LEAN_OBSERVED: ult_basic error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: ult_boundary true"
      else "LEAN_OBSERVED: ult_boundary false"
  | Except.error _ => "LEAN_OBSERVED: ult_boundary error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: slt_boundary_flips true"
      else "LEAN_OBSERVED: slt_boundary_flips false"
  | Except.error _ => "LEAN_OBSERVED: slt_boundary_flips error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: ult_irrefl true"
      else "LEAN_OBSERVED: ult_irrefl false"
  | Except.error _ => "LEAN_OBSERVED: ult_irrefl error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: slt_neg1_lt_0 true"
      else "LEAN_OBSERVED: slt_neg1_lt_0 false"
  | Except.error _ => "LEAN_OBSERVED: slt_neg1_lt_0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: ult_0_lt_ff true"
      else "LEAN_OBSERVED: ult_0_lt_ff false"
  | Except.error _ => "LEAN_OBSERVED: ult_0_lt_ff error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: sle_min_neg1 true"
      else "LEAN_OBSERVED: sle_min_neg1 false"
  | Except.error _ => "LEAN_OBSERVED: sle_min_neg1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: ule_refl true"
      else "LEAN_OBSERVED: ule_refl false"
  | Except.error _ => "LEAN_OBSERVED: ule_refl error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: sle_refl true"
      else "LEAN_OBSERVED: sle_refl false"
  | Except.error _ => "LEAN_OBSERVED: sle_refl error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: ugt_basic true"
      else "LEAN_OBSERVED: ugt_basic false"
  | Except.error _ => "LEAN_OBSERVED: ugt_basic error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: ugt_boundary true"
      else "LEAN_OBSERVED: ugt_boundary false"
  | Except.error _ => "LEAN_OBSERVED: ugt_boundary error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: sgt_boundary true"
      else "LEAN_OBSERVED: sgt_boundary false"
  | Except.error _ => "LEAN_OBSERVED: sgt_boundary error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: uge_refl true"
      else "LEAN_OBSERVED: uge_refl false"
  | Except.error _ => "LEAN_OBSERVED: uge_refl error"

#reduce match Observed with
  | Except.ok v =>
      bif v[13]'(by decide) then "LEAN_OBSERVED: sge_refl true"
      else "LEAN_OBSERVED: sge_refl false"
  | Except.error _ => "LEAN_OBSERVED: sge_refl error"

#reduce match Observed with
  | Except.ok v =>
      bif v[14]'(by decide) then "LEAN_OBSERVED: uge_strict true"
      else "LEAN_OBSERVED: uge_strict false"
  | Except.error _ => "LEAN_OBSERVED: uge_strict error"

#reduce match Observed with
  | Except.ok v =>
      bif v[15]'(by decide) then "LEAN_OBSERVED: sge_strict true"
      else "LEAN_OBSERVED: sge_strict false"
  | Except.error _ => "LEAN_OBSERVED: sge_strict error"

#reduce match Observed with
  | Except.ok v =>
      bif v[16]'(by decide) then "LEAN_OBSERVED: uext true"
      else "LEAN_OBSERVED: uext false"
  | Except.error _ => "LEAN_OBSERVED: uext error"

#reduce match Observed with
  | Except.ok v =>
      bif v[17]'(by decide) then "LEAN_OBSERVED: sext_neg true"
      else "LEAN_OBSERVED: sext_neg false"
  | Except.error _ => "LEAN_OBSERVED: sext_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[18]'(by decide) then "LEAN_OBSERVED: sext_pos true"
      else "LEAN_OBSERVED: sext_pos false"
  | Except.error _ => "LEAN_OBSERVED: sext_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[19]'(by decide) then "LEAN_OBSERVED: pop_f0 true"
      else "LEAN_OBSERVED: pop_f0 false"
  | Except.error _ => "LEAN_OBSERVED: pop_f0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[20]'(by decide) then "LEAN_OBSERVED: pop_00 true"
      else "LEAN_OBSERVED: pop_00 false"
  | Except.error _ => "LEAN_OBSERVED: pop_00 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[21]'(by decide) then "LEAN_OBSERVED: pop_ff true"
      else "LEAN_OBSERVED: pop_ff false"
  | Except.error _ => "LEAN_OBSERVED: pop_ff error"

#reduce match Observed with
  | Except.ok v =>
      bif v[22]'(by decide) then "LEAN_OBSERVED: pop_80 true"
      else "LEAN_OBSERVED: pop_80 false"
  | Except.error _ => "LEAN_OBSERVED: pop_80 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[23]'(by decide) then "LEAN_OBSERVED: pop_55 true"
      else "LEAN_OBSERVED: pop_55 false"
  | Except.error _ => "LEAN_OBSERVED: pop_55 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[24]'(by decide) then "LEAN_OBSERVED: clz_0f true"
      else "LEAN_OBSERVED: clz_0f false"
  | Except.error _ => "LEAN_OBSERVED: clz_0f error"

#reduce match Observed with
  | Except.ok v =>
      bif v[25]'(by decide) then "LEAN_OBSERVED: clz_00 true"
      else "LEAN_OBSERVED: clz_00 false"
  | Except.error _ => "LEAN_OBSERVED: clz_00 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[26]'(by decide) then "LEAN_OBSERVED: clz_80 true"
      else "LEAN_OBSERVED: clz_80 false"
  | Except.error _ => "LEAN_OBSERVED: clz_80 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[27]'(by decide) then "LEAN_OBSERVED: clz_01 true"
      else "LEAN_OBSERVED: clz_01 false"
  | Except.error _ => "LEAN_OBSERVED: clz_01 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[28]'(by decide) then "LEAN_OBSERVED: ctz_f0 true"
      else "LEAN_OBSERVED: ctz_f0 false"
  | Except.error _ => "LEAN_OBSERVED: ctz_f0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[29]'(by decide) then "LEAN_OBSERVED: ctz_00 true"
      else "LEAN_OBSERVED: ctz_00 false"
  | Except.error _ => "LEAN_OBSERVED: ctz_00 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[30]'(by decide) then "LEAN_OBSERVED: ctz_01 true"
      else "LEAN_OBSERVED: ctz_01 false"
  | Except.error _ => "LEAN_OBSERVED: ctz_01 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[31]'(by decide) then "LEAN_OBSERVED: ctz_80 true"
      else "LEAN_OBSERVED: ctz_80 false"
  | Except.error _ => "LEAN_OBSERVED: ctz_80 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[32]'(by decide) then "LEAN_OBSERVED: lg2_00 true"
      else "LEAN_OBSERVED: lg2_00 false"
  | Except.error _ => "LEAN_OBSERVED: lg2_00 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[33]'(by decide) then "LEAN_OBSERVED: lg2_01 true"
      else "LEAN_OBSERVED: lg2_01 false"
  | Except.error _ => "LEAN_OBSERVED: lg2_01 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[34]'(by decide) then "LEAN_OBSERVED: lg2_02 true"
      else "LEAN_OBSERVED: lg2_02 false"
  | Except.error _ => "LEAN_OBSERVED: lg2_02 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[35]'(by decide) then "LEAN_OBSERVED: lg2_03 true"
      else "LEAN_OBSERVED: lg2_03 false"
  | Except.error _ => "LEAN_OBSERVED: lg2_03 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[36]'(by decide) then "LEAN_OBSERVED: lg2_04 true"
      else "LEAN_OBSERVED: lg2_04 false"
  | Except.error _ => "LEAN_OBSERVED: lg2_04 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[37]'(by decide) then "LEAN_OBSERVED: lg2_05 true"
      else "LEAN_OBSERVED: lg2_05 false"
  | Except.error _ => "LEAN_OBSERVED: lg2_05 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[38]'(by decide) then "LEAN_OBSERVED: lg2_ff true"
      else "LEAN_OBSERVED: lg2_ff false"
  | Except.error _ => "LEAN_OBSERVED: lg2_ff error"
