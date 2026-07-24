/- RECALIBRATED 2026-07-24 (V-H1): the surface this probe originally
   pinned was retired from the library; the row is now a DELETION PIN —
   see the .shouldfail.expected sidecar for the current contract. -/
/-
Probe pattern: try to use `error` to manufacture a proof of `False`.
SAW's `isort 1` forbids this; our `Sort (u+1)` Lean signature must
also reject it. If this file ever elaborates clean, soundness on
the Lean side is broken.
-/

import CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePrimitives

theorem fake_false : False := error False "boom"
