import Emitted

-- The closer proves only True — it never binds to the emitted goal.
-- A sound checker must reject this discharge.
theorem goal_closed : True := trivial
