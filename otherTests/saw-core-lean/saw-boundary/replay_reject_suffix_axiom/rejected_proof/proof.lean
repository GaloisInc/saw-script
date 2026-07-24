import Emitted

-- A user axiom whose NAME ends in an allowlisted axiom name. The
-- allowlist is exact-match (not suffix), so this rejects — closing
-- the unsoundness the non-implementer review found.
axiom unsound_vecToBitVec_bitVecToVec : goal

theorem goal_closed : goal := unsound_vecToBitVec_bitVecToVec
