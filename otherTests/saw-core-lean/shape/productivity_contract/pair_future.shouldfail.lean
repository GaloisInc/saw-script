/-
Attack pattern: try to discharge the mutual-stream component productivity
contract for a body that reads one recursive stream at a future index.
-/

import CryptolToLean

open CryptolToLean.SAWCorePrimitives

example : PairStreamComponentProductive Bool Bool Bool
    (fun lookupA _lookupB i => lookupA (i + 1)) := by
  saw_productivity
