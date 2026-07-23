import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: shl_1 true"
      else "LEAN_OBSERVED: shl_1 false"
  | Except.error _ => "LEAN_OBSERVED: shl_1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: shl_0 true"
      else "LEAN_OBSERVED: shl_0 false"
  | Except.error _ => "LEAN_OBSERVED: shl_0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: shl_w1 true"
      else "LEAN_OBSERVED: shl_w1 false"
  | Except.error _ => "LEAN_OBSERVED: shl_w1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: shl_w true"
      else "LEAN_OBSERVED: shl_w false"
  | Except.error _ => "LEAN_OBSERVED: shl_w error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: shl_gt_w true"
      else "LEAN_OBSERVED: shl_gt_w false"
  | Except.error _ => "LEAN_OBSERVED: shl_gt_w error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: shl_2w true"
      else "LEAN_OBSERVED: shl_2w false"
  | Except.error _ => "LEAN_OBSERVED: shl_2w error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: shr_1 true"
      else "LEAN_OBSERVED: shr_1 false"
  | Except.error _ => "LEAN_OBSERVED: shr_1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: shr_0 true"
      else "LEAN_OBSERVED: shr_0 false"
  | Except.error _ => "LEAN_OBSERVED: shr_0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: shr_w1 true"
      else "LEAN_OBSERVED: shr_w1 false"
  | Except.error _ => "LEAN_OBSERVED: shr_w1 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: shr_w true"
      else "LEAN_OBSERVED: shr_w false"
  | Except.error _ => "LEAN_OBSERVED: shr_w error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: shr_gt_w true"
      else "LEAN_OBSERVED: shr_gt_w false"
  | Except.error _ => "LEAN_OBSERVED: shr_gt_w error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: sshr_1_neg true"
      else "LEAN_OBSERVED: sshr_1_neg false"
  | Except.error _ => "LEAN_OBSERVED: sshr_1_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: sshr_0 true"
      else "LEAN_OBSERVED: sshr_0 false"
  | Except.error _ => "LEAN_OBSERVED: sshr_0 error"

#reduce match Observed with
  | Except.ok v =>
      bif v[13]'(by decide) then "LEAN_OBSERVED: sshr_w1_neg true"
      else "LEAN_OBSERVED: sshr_w1_neg false"
  | Except.error _ => "LEAN_OBSERVED: sshr_w1_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[14]'(by decide) then "LEAN_OBSERVED: sshr_w_neg true"
      else "LEAN_OBSERVED: sshr_w_neg false"
  | Except.error _ => "LEAN_OBSERVED: sshr_w_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[15]'(by decide) then "LEAN_OBSERVED: sshr_big_neg true"
      else "LEAN_OBSERVED: sshr_big_neg false"
  | Except.error _ => "LEAN_OBSERVED: sshr_big_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[16]'(by decide) then "LEAN_OBSERVED: sshr_w1_pos true"
      else "LEAN_OBSERVED: sshr_w1_pos false"
  | Except.error _ => "LEAN_OBSERVED: sshr_w1_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[17]'(by decide) then "LEAN_OBSERVED: sshr_1_pos true"
      else "LEAN_OBSERVED: sshr_1_pos false"
  | Except.error _ => "LEAN_OBSERVED: sshr_1_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[18]'(by decide) then "LEAN_OBSERVED: not_pattern true"
      else "LEAN_OBSERVED: not_pattern false"
  | Except.error _ => "LEAN_OBSERVED: not_pattern error"

#reduce match Observed with
  | Except.ok v =>
      bif v[19]'(by decide) then "LEAN_OBSERVED: and_pattern true"
      else "LEAN_OBSERVED: and_pattern false"
  | Except.error _ => "LEAN_OBSERVED: and_pattern error"

#reduce match Observed with
  | Except.ok v =>
      bif v[20]'(by decide) then "LEAN_OBSERVED: or_pattern true"
      else "LEAN_OBSERVED: or_pattern false"
  | Except.error _ => "LEAN_OBSERVED: or_pattern error"

#reduce match Observed with
  | Except.ok v =>
      bif v[21]'(by decide) then "LEAN_OBSERVED: xor_pattern true"
      else "LEAN_OBSERVED: xor_pattern false"
  | Except.error _ => "LEAN_OBSERVED: xor_pattern error"

#reduce match Observed with
  | Except.ok v =>
      bif v[22]'(by decide) then "LEAN_OBSERVED: xor_self true"
      else "LEAN_OBSERVED: xor_self false"
  | Except.error _ => "LEAN_OBSERVED: xor_self error"

#reduce match Observed with
  | Except.ok v =>
      bif v[23]'(by decide) then "LEAN_OBSERVED: and_not_self true"
      else "LEAN_OBSERVED: and_not_self false"
  | Except.error _ => "LEAN_OBSERVED: and_not_self error"

#reduce match Observed with
  | Except.ok v =>
      bif v[24]'(by decide) then "LEAN_OBSERVED: or_not_self true"
      else "LEAN_OBSERVED: or_not_self false"
  | Except.error _ => "LEAN_OBSERVED: or_not_self error"
