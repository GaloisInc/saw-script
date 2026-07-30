# The wave-3 `bitvector` type-collapse claim is WRONG (verified 2026-07-30)

Pending: fold into TODO.md once the concurrent fix re-audit releases that file.

## The claim

Wave 3's completeness critic, via the lib-w2-2 lane, asserted that the
type-collapse class (Float/Double/IntMod/Integer/Rational) has an
unswept sixth member: **`bitvector`** (`SpecialTreatment.hs:685` →
`SAWCoreBitvectors.lean:32`), and cited it as vindication of the
convergence proposal's §6 hedge ("I cannot enumerate reliably even
when specifically trying to"). I repeated that in the wave-3 report
§1 and listed "seal `bitvector`" as an emission-path release blocker.

## Why it is wrong

The class requires an **opaque SAWCore primitive** (no reduction rule
identifying it with anything) paired with a **reducible Lean alias**,
so that two SAW-DISTINCT types become Lean-defeq and `unsafeAssert`'s
`rfl` arm self-discharges. `bitvector` has no such pairing, because
**SAWCore has no `bitvector` at all**:

| name | SAWCore declaration | verdict |
|---|---|---|
| `Vec` | `primitive Vec : Nat -> sort 0 -> sort 0;` (Prelude.sawcore:1530) | real, opaque |
| `IntMod` | `primitive IntMod : Nat -> sort 0;` (Prelude.sawcore:2126) | real, opaque — the confirmed member |
| `bitvector` | **none** — appears only in comments | dead key |
| `Bit` | **none** | dead key |

Instrument controlled: the same search that returns zero for
`bitvector` returns the `Vec` and `IntMod` declarations, so the zero is
a real absence and not a bad grep. The entry is in
`sawCorePreludeSpecialTreatmentMap` (line 535+), which is keyed by
SAWCore Prelude short names, so SAWCore is the right namespace to
search.

Empirically dead as well:

- `bitvector` appears in **0** emitted corpus artifacts
  (`grep -rlw bitvector --include=*.lean.good otherTests/`).
- The support-library `abbrev bitvector` is referenced nowhere outside
  its own definition file (other hits are prose in comments).
- The only Haskell occurrence is the treatment entry itself.

With no SAWCore type to misrepresent, nothing is being collapsed. The
`abbrev` is a support-library convenience alias that no SAWCore
reduction rule contradicts.

## Consequence

**Do NOT seal `bitvector`.** Converting the `abbrev` to a `structure`
would change the support library, could break any future artifact that
used the alias, and buys zero soundness. It would be cargo-cult work
justified by a mis-derived class membership.

**The type-collapse class stands at five members, closed.** My "exactly
five" claim in the IntMod seal was right; the wave-3 refutation of it
was wrong. This does NOT rescue the convergence proposal's §5
prediction — that remains REFUTED on the other three independent
counts (K-2 chokepoint CRITICAL, W2-UNRUN-1 chokepoint CRITICAL, K-1
outside the six enumerations) — but §6's specific "I found a sixth
member" vindication should be withdrawn.

## What IS real here (LOW)

Two dead treatment entries, `Bit` and `bitvector`, whose in-place
comment asserts routing behaviour that can never occur ("Haskell
should route to the checked support declaration rather than replacing
it with a Lean-core type directly" — the key never matches, so no
routing happens). Same family as wave-3's F-W3-HE-3 (three `skip`
rows naming non-existent Lean realisations) and as the dead `carrier`
guard the fix audit found in my own gate-3 code.

Fix: delete both entries and the dead `abbrev`, or — better, since
this is the third instance of the same family — add a derived check
that every `sawCorePreludeSpecialTreatmentMap` key resolves to a real
SAWCore Prelude declaration. That check is the mechanism; deleting two
entries is the instance. `auditLeanOpaqueDeadEntries` (landed
2026-07-29) already does exactly this for `leanOpaqueBuiltins`, so the
shape is proven and cheap to extend.

## Method note

This is the second time in two days that verifying an audit's claim
before acting on it changed the action — the first being the fix audit
finding my gate over-refused. Audits are evidence, not instructions.
