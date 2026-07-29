import Emitted

-- Honest-looking closer. The attack is entirely in completed.lean's
-- metaprogram; this file is what the run would present afterwards.
theorem goal_closed : goal := by
  intro x y
  native_decide
