/-
Attack pattern: try to use `error` to manufacture a proof of `False`.
SAW's `isort 1` forbids this; our `Sort (u+1)` Lean signature must
also reject it. If this file ever elaborates clean, soundness on
the Lean side is broken.
-/

import CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePrimitives

theorem fake_false : False := error False "boom"
