# archive

Trajectory docs from saw-core-lean's earlier phases. Useful as
historical record (the project went through two failed attempts
— P4 v2 universe-polymorphic, P6 Prop-typed — before landing on
the specialization-mode design that ships today). Read in
chronological order to follow the design evolution.

These are no longer load-bearing — current information lives in
the top-level `doc/` files:

- `architecture.md` — current as-of-today design reference.
- `getting-started.md` — user walkthrough.
- `contributing.md` — how to extend.
- `2026-04-24_soundness-boundaries.md` — canonical trust contract.
- `2026-05-02_post-audit-plan.md` — current plan-of-record.
- `2026-05-02_semantic-testing-investigation.md` — Phase 3
  investigation into Rocq parity.

If a claim in an archived doc conflicts with the current source
code or with one of the top-level docs, **trust the current
sources**. The archive is preserved for context, not as a
running specification.

Files here:

- `2026-04-22_*` — pre-pivot phase analyses, including the failed
  P4 v2 (universe-polymorphic) and P6 (Prop-typed) attempts.
- `2026-04-23_*` — specialization-pivot design and stage breakdown.
- `2026-04-24_audit-*` — the original deep-dive audits (Nat
  mapping, primitive fidelity) that informed soundness-boundaries.md.
- `2026-05-01_*` — Phase 4 (Cryptol coverage) status and the
  BitVec-binding deferral decision.
