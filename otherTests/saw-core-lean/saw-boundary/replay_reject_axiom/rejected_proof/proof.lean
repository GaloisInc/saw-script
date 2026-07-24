import Emitted

-- A user-declared axiom of the goal type: an unsound closer the
-- axiom audit must reject (not on the allowlist).
axiom unsound_axiom : goal

theorem goal_closed : goal := unsound_axiom
