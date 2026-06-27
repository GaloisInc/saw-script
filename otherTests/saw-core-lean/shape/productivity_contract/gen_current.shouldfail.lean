/-
Attack pattern: try to discharge the bounded-vector productivity contract for
a body that reads the recursive vector at the current index.

If this elaborates, `saw_productivity` can justify observable uses of the
genFixM fallback default.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives

example : GenFixBodyProductive Bool
    (fun lookup i => Pure.pure (lookup i)) := by
  saw_productivity
