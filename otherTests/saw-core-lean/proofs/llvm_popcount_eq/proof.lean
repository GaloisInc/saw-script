/-
LLVM popcount (Hacker's Delight SWAR) vs Cryptol popCount — native-eval
trust tier row (see completed.lean header and .trust-tier). goal_holds
carries the discharge; the SWAR residue closes by bv_decide.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
