/-
Salsa20 quarterround verify — native-eval trust tier row (see
completed.lean header and .trust-tier). goal_holds carries the
discharge; the 32-bit quarterround equation closes by bv_decide.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
