/-
Salsa20 doubleround via SAW-side composition — STRICT-tier residual
(see completed.lean header). Both sides are the same Cryptol
composition, so the discharge is normalization + reflexivity.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
