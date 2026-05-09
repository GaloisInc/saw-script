-- Umbrella module for the saw-lean-example discharges.
-- `lake build` elaborates both sub-modules; each asserts its
-- hand-written tactic proof closes the corresponding emitted goal.
import Proofs.Invol
import Proofs.Eq
