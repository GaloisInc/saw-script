import Emitted

-- z-arm select AND successor-arm predecessor plumbing: natCaseRaw's
-- s receives the predecessor, so Observed 3 = s 2 = 2.
#reduce match Observed 0, Observed 3 with
  | 4, 2 => "LEAN_OBSERVED: zero-arm 4 succ-arm pred 2"
  | _, _ => "LEAN_OBSERVED: wrong arm values"
