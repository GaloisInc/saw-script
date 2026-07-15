import CryptolToLean

open CryptolToLean.SAWCorePrimitives

def weakFixBody : Except String Bool -> Except String Bool
  | Except.ok false => Except.ok false
  | Except.ok true => Except.ok false
  | Except.error msg => Except.error msg

/- This proof would elaborate if `saw_fix_unique_exists` only required
uniqueness among successful `Except.ok` fixed points. The strengthened contract
must reject it because every `Except.error msg` is also a fixed point. -/
example : saw_fix_unique_exists Bool weakFixBody := by
  exists false
  constructor
  · rfl
  · intro y hy
    cases y <;> simp [weakFixBody] at hy ⊢
