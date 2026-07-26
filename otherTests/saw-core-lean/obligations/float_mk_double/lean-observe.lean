import Emitted

open CryptolToLean.SAWCorePrimitives

/- F-2 (2026-07-25). See the companion note in
`obligations/float_mk_float/lean-observe.lean` for why the pair
destructuring is gone: it was reading the type-image collapse that
made `mkFloat m e = mkDouble m e` `rfl`-provable in Lean and
underivable in SAW.

`observed_link` additionally pins the faithful ODDITY this row
exists to record: SAW's own `mkDouble` primitive RETURNS `Float`
(`Prelude.sawcore:2163`), and the binding preserves that rather than
silently "correcting" it. The theorem's type is
`Except String Float`, so a future correction to `Double` fails to
compile here — which is the point. -/

/-- The emitted term is exactly `mkDouble 6 7`, arguments pinned,
and its type is `Except String Float` (SAW's declared return type
for `mkDouble`, not `Double`). `Float` is written FULLY QUALIFIED
for the same reason emission qualifies it (`mapsToQualifiedTie`):
the short name ties with Lean core's `_root_.Float`. -/
theorem observed_link :
    Observed =
      (Pure.pure (mkDouble 6 7) :
        Except String CryptolToLean.SAWCorePrimitives.Float) := rfl

#reduce match Observed with
  | Except.ok _ => "LEAN_OBSERVED: mkDouble 6 7"
  | Except.error err => "LEAN_OBSERVED: error: " ++ err
