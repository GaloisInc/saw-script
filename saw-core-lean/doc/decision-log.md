# Decision Log

Living record of ratified design decisions. Moved out of TODO.md
in the 2026-07-17 doc reorganization.

- [x] Treat Lean as a proof backend, not just an emitter.
- [x] Treat Rocq feature parity as the top-level feature goal; proof discharge
  is required but not exclusive.
- [x] Preserve SAWCore errors with `Except String`.
- [x] Reject unsupported primitives by default.
- [x] Remove the old emitted-Lean result-shape classifier.
- [x] Remove broadly defaulting stream helpers from the Lean support library.
- [x] Treat soundness-side conditions as emitted Lean obligations, not Haskell
  automation requirements.
- [x] Treat Haskell semantic classifiers as migration scaffolding, not the
  trusted long-term design. When a classifier justifies recursion,
  productivity, totality, or rawification, prefer moving that justification into
  Lean as a named theorem, checked helper, or tactic-proved obligation.
- [x] Permit classifiers as untrusted proof emitters: they may recognize a
  generated shape and emit helpful Lean lemmas/scripts, provided the backend
  still emits the regular contract and trusts only the kernel-checked evidence.
- [x] Treat arbitrary SAWCore `Prelude.fix` as in scope for emit-stage
  proof-carrying translation via an explicit unique-fixed-point obligation.
  This does not mean arbitrary fix is automatically discharged.
- [x] Prioritize emission correctness and stable generated Lean before adding
  integrated SAW-side proof-check UX.
- [x] Split auto-emitted Prelude declarations into raw logical definitions and
  wrapped value-domain facades.
- [x] Reject `bv_decide`/`bv_check` as accepted proof-discharge mechanisms under
  the current no-extra-trust policy, because substantial uses introduce
  proof-local native-evaluation axioms. Use checked Lean proof automation
  (`grind`, `simp`, `omega`/`bv_omega`, `cbv`, helper lemmas) where it works,
  and leave hard BV obligations open rather than widening the trusted base.
- [x] Decide and start encoding the position/callee convention design before
  further local wrapping fixes. The 2026-07-03 raw-logical slice introduced the
  explicit convention vocabulary and routed `Eq`/`Refl`/`Eq.rec` through it.
  Remaining convention surfaces should extend this design by new declared
  positions/callee contracts, not by local patches.

