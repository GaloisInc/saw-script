import Emitted

open CryptolToLean.SAWCorePrimitives

/- F-2 (2026-07-25). This observer used to destructure `Observed` as
an `Int × Int` pair and check the components against 1 and 2. That
observation was READING THE BUG: `Float` was bound to `Int × Int`
and `mkFloat` to the pair constructor, which is exactly the collapse
that made `Eq Float (mkFloat m e) (mkDouble m e)` — underivable in
SAW — provable by `rfl` in Lean. `Float` is now a sealed abstract
type with an uninterpreted constructor, matching what SAW declares,
so the components are no longer observable from Lean. They are not
observable from SAW either: the Prelude declares no operation that
projects them.

The observation is rebuilt in two parts and is STRONGER on the part
that survives:

  1. `observed_link` — a KERNEL-CHECKED equality pinning the emitted
     term to `mkFloat 1 2` exactly, arguments included. The old
     `bif`-on-components form could only report "wrong pair"; this
     fails to COMPILE if either argument drifts.
  2. `#reduce` on the `Except` layer, producing the LEAN_OBSERVED
     line the harness diffs against SAW. That layer is still
     concrete, so an error-vs-ok divergence is still caught.

Non-vacuity: (1) is a real defeq check against a literal, not an
assertion about `Observed`; (2) prints from `Observed` itself. A
wrong argument fails at (1); a thrown error changes the printed line
at (2). -/

/-- The emitted term is exactly `mkFloat 1 2`, arguments pinned. -/
theorem observed_link : Observed = Pure.pure (mkFloat 1 2) := rfl

#reduce match Observed with
  | Except.ok _ => "LEAN_OBSERVED: mkFloat 1 2"
  | Except.error err => "LEAN_OBSERVED: error: " ++ err
