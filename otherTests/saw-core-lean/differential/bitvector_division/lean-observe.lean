import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: udiv_basic true"
      else "LEAN_OBSERVED: udiv_basic false"
  | Except.error _ => "LEAN_OBSERVED: udiv_basic error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: urem_basic true"
      else "LEAN_OBSERVED: urem_basic false"
  | Except.error _ => "LEAN_OBSERVED: urem_basic error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: udiv_by1 true"
      else "LEAN_OBSERVED: udiv_by1 false"
  | Except.error _ => "LEAN_OBSERVED: udiv_by1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: urem_by1 true"
      else "LEAN_OBSERVED: urem_by1 false"
  | Except.error _ => "LEAN_OBSERVED: urem_by1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: udiv_self true"
      else "LEAN_OBSERVED: udiv_self false"
  | Except.error _ => "LEAN_OBSERVED: udiv_self error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: udiv_small_big true"
      else "LEAN_OBSERVED: udiv_small_big false"
  | Except.error _ => "LEAN_OBSERVED: udiv_small_big error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: urem_small_big true"
      else "LEAN_OBSERVED: urem_small_big false"
  | Except.error _ => "LEAN_OBSERVED: urem_small_big error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: udiv_msb_set true"
      else "LEAN_OBSERVED: udiv_msb_set false"
  | Except.error _ => "LEAN_OBSERVED: udiv_msb_set error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: udiv_ff_ff true"
      else "LEAN_OBSERVED: udiv_ff_ff false"
  | Except.error _ => "LEAN_OBSERVED: udiv_ff_ff error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: sdiv_pp true"
      else "LEAN_OBSERVED: sdiv_pp false"
  | Except.error _ => "LEAN_OBSERVED: sdiv_pp error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: srem_pp true"
      else "LEAN_OBSERVED: srem_pp false"
  | Except.error _ => "LEAN_OBSERVED: srem_pp error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: sdiv_np true"
      else "LEAN_OBSERVED: sdiv_np false"
  | Except.error _ => "LEAN_OBSERVED: sdiv_np error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: srem_np true"
      else "LEAN_OBSERVED: srem_np false"
  | Except.error _ => "LEAN_OBSERVED: srem_np error"

#reduce match Observed with
  | Except.ok v =>
      bif v[13]'(by decide) then "LEAN_OBSERVED: sdiv_pn true"
      else "LEAN_OBSERVED: sdiv_pn false"
  | Except.error _ => "LEAN_OBSERVED: sdiv_pn error"

#reduce match Observed with
  | Except.ok v =>
      bif v[14]'(by decide) then "LEAN_OBSERVED: srem_pn true"
      else "LEAN_OBSERVED: srem_pn false"
  | Except.error _ => "LEAN_OBSERVED: srem_pn error"

#reduce match Observed with
  | Except.ok v =>
      bif v[15]'(by decide) then "LEAN_OBSERVED: sdiv_nn true"
      else "LEAN_OBSERVED: sdiv_nn false"
  | Except.error _ => "LEAN_OBSERVED: sdiv_nn error"

#reduce match Observed with
  | Except.ok v =>
      bif v[16]'(by decide) then "LEAN_OBSERVED: srem_nn true"
      else "LEAN_OBSERVED: srem_nn false"
  | Except.error _ => "LEAN_OBSERVED: srem_nn error"

#reduce match Observed with
  | Except.ok v =>
      bif v[17]'(by decide) then "LEAN_OBSERVED: sdiv_min_neg1 true"
      else "LEAN_OBSERVED: sdiv_min_neg1 false"
  | Except.error _ => "LEAN_OBSERVED: sdiv_min_neg1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[18]'(by decide) then "LEAN_OBSERVED: srem_min_neg1 true"
      else "LEAN_OBSERVED: srem_min_neg1 false"
  | Except.error _ => "LEAN_OBSERVED: srem_min_neg1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[19]'(by decide) then "LEAN_OBSERVED: sdiv_zero_x true"
      else "LEAN_OBSERVED: sdiv_zero_x false"
  | Except.error _ => "LEAN_OBSERVED: sdiv_zero_x error"

#reduce match Observed with
  | Except.ok v =>
      bif v[20]'(by decide) then "LEAN_OBSERVED: sdiv_by1 true"
      else "LEAN_OBSERVED: sdiv_by1 false"
  | Except.error _ => "LEAN_OBSERVED: sdiv_by1 error"
