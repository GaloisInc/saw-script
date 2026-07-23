import Emitted

-- Pairwise labeled observer for the edge-case matrix (2026-07-23).
-- One #reduce per case, projecting index i of the emitted vector;
-- output order matches the SAW_OBSERVED print order in test.saw.

#reduce match Observed with
  | Except.ok v =>
      bif v[0]'(by decide) then "LEAN_OBSERVED: le true"
      else "LEAN_OBSERVED: le false"
  | Except.error _ => "LEAN_OBSERVED: le error"

#reduce match Observed with
  | Except.ok v =>
      bif v[1]'(by decide) then "LEAN_OBSERVED: lt true"
      else "LEAN_OBSERVED: lt false"
  | Except.error _ => "LEAN_OBSERVED: lt error"

#reduce match Observed with
  | Except.ok v =>
      bif v[2]'(by decide) then "LEAN_OBSERVED: add true"
      else "LEAN_OBSERVED: add false"
  | Except.error _ => "LEAN_OBSERVED: add error"

#reduce match Observed with
  | Except.ok v =>
      bif v[3]'(by decide) then "LEAN_OBSERVED: sub true"
      else "LEAN_OBSERVED: sub false"
  | Except.error _ => "LEAN_OBSERVED: sub error"

#reduce match Observed with
  | Except.ok v =>
      bif v[4]'(by decide) then "LEAN_OBSERVED: mul true"
      else "LEAN_OBSERVED: mul false"
  | Except.error _ => "LEAN_OBSERVED: mul error"

#reduce match Observed with
  | Except.ok v =>
      bif v[5]'(by decide) then "LEAN_OBSERVED: neg true"
      else "LEAN_OBSERVED: neg false"
  | Except.error _ => "LEAN_OBSERVED: neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[6]'(by decide) then "LEAN_OBSERVED: recip true"
      else "LEAN_OBSERVED: recip false"
  | Except.error _ => "LEAN_OBSERVED: recip error"

#reduce match Observed with
  | Except.ok v =>
      bif v[7]'(by decide) then "LEAN_OBSERVED: floor_pos true"
      else "LEAN_OBSERVED: floor_pos false"
  | Except.error _ => "LEAN_OBSERVED: floor_pos error"

#reduce match Observed with
  | Except.ok v =>
      bif v[8]'(by decide) then "LEAN_OBSERVED: floor_neg true"
      else "LEAN_OBSERVED: floor_neg false"
  | Except.error _ => "LEAN_OBSERVED: floor_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[9]'(by decide) then "LEAN_OBSERVED: floor_neg_exact true"
      else "LEAN_OBSERVED: floor_neg_exact false"
  | Except.error _ => "LEAN_OBSERVED: floor_neg_exact error"

#reduce match Observed with
  | Except.ok v =>
      bif v[10]'(by decide) then "LEAN_OBSERVED: floor_neg_small true"
      else "LEAN_OBSERVED: floor_neg_small false"
  | Except.error _ => "LEAN_OBSERVED: floor_neg_small error"

#reduce match Observed with
  | Except.ok v =>
      bif v[11]'(by decide) then "LEAN_OBSERVED: neg_denom true"
      else "LEAN_OBSERVED: neg_denom false"
  | Except.error _ => "LEAN_OBSERVED: neg_denom error"

#reduce match Observed with
  | Except.ok v =>
      bif v[12]'(by decide) then "LEAN_OBSERVED: unreduced true"
      else "LEAN_OBSERVED: unreduced false"
  | Except.error _ => "LEAN_OBSERVED: unreduced error"

#reduce match Observed with
  | Except.ok v =>
      bif v[13]'(by decide) then "LEAN_OBSERVED: recip_neg true"
      else "LEAN_OBSERVED: recip_neg false"
  | Except.error _ => "LEAN_OBSERVED: recip_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[14]'(by decide) then "LEAN_OBSERVED: lt_neg true"
      else "LEAN_OBSERVED: lt_neg false"
  | Except.error _ => "LEAN_OBSERVED: lt_neg error"

#reduce match Observed with
  | Except.ok v =>
      bif v[15]'(by decide) then "LEAN_OBSERVED: recip_recip true"
      else "LEAN_OBSERVED: recip_recip false"
  | Except.error _ => "LEAN_OBSERVED: recip_recip error"
