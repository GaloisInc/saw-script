/-
Attack pattern: try to discharge the mutual-stream component productivity
contract for a body that reads one recursive stream at the current index.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives

example : PairStreamComponentProductive Bool Bool Bool
    (fun lookupA _lookupB i => lookupA i) := by
  saw_productivity
