# Design note: the two remaining hand enumerations share one root (2026-07-29)

Scopes the two conversions the convergence proposal (§7.2) called
"the real work": the `hardcodedBareNames` residue and
`leanOpaqueBuiltins`. Written after the three cheap conversions
landed; nothing here is implemented yet.

## 1. The shared root

Both lists exist because **a name can enter the emitter's output
without registering itself anywhere**:

- The emitter writes some Lean names as string literals at the point
  of use — `Lean.Ident "Pure.pure"`, `Lean.Ident "h_proof_"`, and so
  on. There are currently **128 inline `Lean.Ident "…"` spellings in
  `saw-core-lean/src/SAWCoreLean/`**. `hardcodedBareNames`
  (SpecialTreatment.hs) is a hand-mirror of the subset that matters
  for capture analysis, and nothing connects the mirror to the
  spellings.
- The treatment table can route a SAWCore name to a handwritten Lean
  realisation without recording whether `scNormalize` is allowed to
  unfold the SAWCore body first. `leanOpaqueBuiltins`
  (`saw-central/src/SAWCentral/Prover/Exporter.hs` — NOT
  SpecialTreatment.hs as the proposal's table said) is a hand-mirror
  of the "must not unfold" subset, and nothing connects it to the
  treatment entries it protects.

Both mirrors are exactly the enumeration style that failed five times
(proposal §2): correct when written, no reason to change when the
code grows.

## 2. What each list actually protects

**`hardcodedBareNames`** feeds `emitterBareNames`, the capture-
avoidance set: a user binder that shadows a name the emitter
REFERENCES gets renamed (`freshVariant`). A missing entry means a
user binder named e.g. `vecSequenceM` silently captures the
emitter's reference — the W2-MAP-1 class. The treatment-derived and
contract-derived parts are already derived (2026-07-29); the residue
is precisely the point-of-use string literals.

**`leanOpaqueBuiltins`** feeds `scNormalizeForLean`'s don't-unfold
set. Its recursor-hazard members are already auto-derived
(`discoverNatRecReachers`, `discoverEnumEncodingReachers` — the L-3
promotion). The un-derived residue is the *realisation-bypass*
members: defs whose SAWCore body would unfold into something the
translator emits wrongly or opaquely, where the handwritten Lean
realisation must be used instead. The canonical hazard is L-16:
`ite`'s body uses `Bool#rec` with SAW's True-first argument order;
unfolding emits `@Bool.rec` read by Lean in False-first order —
branches silently swapped. A new Prelude def with a handwritten
realisation and no opacity entry re-opens that class.

## 3. Proposed mechanism, in two stages each

### 3a. `hardcodedBareNames` residue

**Stage 1 (lint, derivable today).** A smoketest lint that scans
`src/SAWCoreLean/*.hs` for `Lean.Ident "` string literals outside a
single registry module and fails on any spelling whose name is
neither (a) in `hardcodedBareNames`, (b) a generated-binder prefix
(`x__`, `h_*_`, `scrut_`, … — the shadowers, deliberately excluded
per the 2026-07-26 NOTE), nor (c) in the treatment/contract-derived
sets. This makes the mirror checkable against the spellings it
mirrors — the same move as the waiver-evidence audit. It reuses
`lintSourceFiles` (derived walk) so new modules are covered
automatically.

**Stage 2 (by construction).** Split `Lean.Ident` construction into
two paths: generated binders (fresh names the emitter *introduces*)
and referenced bare names (names the emitter *cites*). The latter
become constants exported from one registry module whose table IS
`hardcodedBareNames` — single source, so a bare citation cannot be
spelled without joining the capture set. This is the `adaptTo` move:
the forbidden thing (an unregistered citation) becomes
unrepresentable. Cost: touching ~128 sites, mechanical but wide;
the payoff is deleting the mirror entirely.

Stage 1 is worth doing before wave 3. Stage 2 is post-0.02 work.

### 3b. `leanOpaqueBuiltins` residue

**Direction 1 (dead-entry check, cheap).** Every entry must resolve
in the loaded Prelude (`scResolveName` non-empty) at translator
startup or in a smoketest. A renamed SAWCore primitive currently
strips its protection silently — the classic dead-waiver rot.

**Direction 2 (coverage check, the real one).** At SAW-init time,
walk the module map: every Prelude `Def` **with a body** whose
use-site treatment routes to a handwritten realisation
(`mapsTo`/`mapsToExpl` into the support-library modules) must be in
the opaque set — via the auto-derives, `leanOpaqueBuiltins`, or an
explicit safe-to-unfold waiver **with a reason the check can state**
(e.g. "body unfolds one step to `ite` and stops there", the
documented `not`/`and`/`or` chain). This mirrors the existing
startup audit that catches treatment-less primitives, and the waiver
shape mirrors the replay selftest's evidence-carrying table.

The check runs where the module map already exists (Exporter.hs
startup / `dumpLeanResidualPrimitives` machinery), so it needs no
new plumbing — only the classifier "is this target handwritten",
which is derivable from the target module of the treatment entry.

## 4. Order and prediction

Do 3b before 3a-stage-2 (it is smaller and guards a soundness class
with a live exploit shape, L-16). If wave 3 runs before these land,
its scorecard (proposal §5) predicts any CRITICAL it finds lands in
one of these two enumerations — that prediction stays falsifiable
either way.
