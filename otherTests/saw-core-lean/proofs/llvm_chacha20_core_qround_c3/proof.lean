/-
ChaCha20 core-round quarterround verify — native-eval trust tier row
(see completed.lean header and .trust-tier). goal_holds carries the
discharge; the four qround equations close by bv_decide.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
