/-
Attack pattern: try to discharge the bounded-vector productivity contract for
a body that reads the recursive vector at a future index.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives

example : GenFixBodyProductive Bool
    (fun lookup i => Pure.pure (lookup (i + 1))) := by
  saw_productivity
