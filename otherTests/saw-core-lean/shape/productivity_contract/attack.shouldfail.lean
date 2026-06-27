/-
Attack pattern: try to discharge the stream-fix productivity contract for a
body that reads the recursive stream at the current index.

If this elaborates, `saw_productivity` has become too strong and can justify
observable uses of the fix fallback default.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives

example : StreamBodyProductive Bool (fun lookup i => lookup i) := by
  saw_productivity
