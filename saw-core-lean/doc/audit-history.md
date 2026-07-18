# Audit History

Living index of the adversarial audits that shaped the backend.
Moved out of TODO.md in the 2026-07-17 doc reorganization.

Three adversarial audits shaped the current priorities. Full reports:
`doc/archive/2026-06-28_clever-legacy-path-audit.md`,
`doc/archive/2026-06-29_comprehensive-audit.md`, and the 2026-07-01 audit summary. Most
of their immediate blockers are resolved: `classifyPolyStreamIterate`,
`FixShapes`, and `rawifyExceptToRaw` are removed; the `bvLg2` ceiling-log and
bitvector zero-divisor semantics are fixed (routed through proof-carrying
checked helpers); the harness-validity issues that were Priority 0 (ignored
differential observers, stale-artifact inspection, completed-proof drift,
known-gaps-look-green) are closed. The convergence signal the audits called for
— reducing known-gap *families* through declarative contract tables rather than
patching individual examples — remains the correct measure of progress.

Still-live items carried into the priorities above and the operative plan:

- Silent-unsoundness surfaces (the deep focus): equality subject representation,
  `Eq.rec` proof transport, and recursor constructor-order trust — Operative
  Priority (position-directed translation).
- TCB shrink: prove or isolate the two Vec/BitVec round-trip axioms; replace or
  make proof-carrying `scLiteralFold`; decide whether imported realizations need
  semantic theorems beyond type-checking — Priority 2.
- Raw Lean injection policy: `InjectCodeDecl "Lean"` must not remain an ordinary
  untrusted path to arbitrary emitted Lean — Priority 2.
- SAW-side `offline_lean` replay — DONE 2026-07-16 (`offline_lean_replay`
  discharges goals via the factored trust kernel; exporter stays emit-only) —
  Priority 5. Remaining: CI-harness rebase onto the factored checker;
  binder-type telescope comparison.

Known-gap backlog triage (still current):

- High priority: proof-primitive obligations (`proof_coerce_eq`,
  `proof_bv_eq_to_eq_nat`, `proof_prove_le_nat`, `proof_nat_compare_le`,
  BV/order bridges, vector/fold lemmas, conditional-congruence); direct
  recursor / datatype / list surfaces (`recursor_*`, `user_datatype_recursor`,
  `list_sort_funs_to`, `cryptol_algebraic_enum`); loaded custom primitive/axiom
  declarations and injected-Lean-code policy.
- Medium priority: differential rows that already expose correct obligations but
  await Lean-side proof support (bounds, branch-guard reflection, constant/
  literal vector bounds, Rational/BV nonzero evidence, derived-index
  arithmetic); stream-helper executable replay (blocked on proof-carrying
  stream/recursor design).
- Low priority / not a completion gate: full SHA512 and BV-heavy crypto proofs;
  broad proof automation and cookbook polish; final SAW-side replay UX, import
  isolation, provenance manifests.

