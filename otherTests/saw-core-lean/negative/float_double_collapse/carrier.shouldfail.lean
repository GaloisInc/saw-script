/-
F-2 pin (audit-2, 2026-07-25). SAW's Prelude declares `Float` and
`Double` as two DISTINCT abstract types with two DISTINCT
uninterpreted constructors and no operations. Phase 9 bound both to
`@[reducible] def … := Int × Int`, so all three claims below became
`rfl` in Lean while remaining underivable in SAW — a demonstrable
type-image collapse.

Each claim must FAIL to elaborate. If this file ever compiles clean,
the collapse is back and SAW-invalid equations are `rfl`-provable
again.

Note this probe pins the SEALING, not the choice of witness type:
the carriers are still built over `Int × Int` for non-emptiness, so
a regression that merely removes `opaque` (or shares one carrier
between the two types) is exactly what turns this row green.
-/

import CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePrimitives

-- The two abstract TYPES must not be identified. `Float` is written
-- FULLY QUALIFIED here for the same reason emission qualifies it
-- (`mapsToQualifiedTie`): the short name ties with Lean core's
-- `_root_.Float`, and an ambiguity error would make this row pass
-- for the wrong reason.

-- SPLIT 2026-07-29 (wave-2 audit). This file carried all three claims
-- at once, which is the S-1 masking defect: the FIRST failing claim
-- makes the row pass, so the other two could have gone green
-- unnoticed. One claim per file now — the same discipline the sibling
-- intmod_type_collapse row was built with.

-- The abstract type must not be its own witness carrier.
theorem float_is_pair :
    CryptolToLean.SAWCorePrimitives.Float = (Int × Int) := rfl
