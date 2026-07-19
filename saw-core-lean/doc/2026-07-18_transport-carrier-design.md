# Value content inside equality transports (the transport corner)

2026-07-18. Status: SCOPING — pre-audit. The LAST rev.cry blocker
and the chacha20 function-carrier corner are the SAME hole, pinned
by differential/cryptol_rev_module and
differential/cryptol_chacha20_core_iterate.

## The two pinned instances

1. rev.cry: `coerce (seq x2 a) (seq n a) (seq_cong1 …) value`
   under an OUTER RawValueMode pass: a natToInt inside the
   transported value splices raw while the motive type-side wraps
   (Nat → Except String Int formal). Audit condition 5's
   stamp/emission divergence, reachable, loud.
2. chacha20 core: `Eq.refl` application mismatch at a WRAPPED
   FUNCTION carrier (seq_cong-style coercion between function
   types) — the transport's carrier translation and the
   transported value's translation disagree.

## Root structure

Equality transports (coerce / Eq.rec / seq_cong family) move VALUE
content along TYPE equalities. Two mode regimes meet:
- The CARRIER (motive) translation is type-side: mode-independent,
  always wraps value-domain Pis and value types (Except arrows).
- The transported VALUE's translation depends on the ambient mode:
  under phase-beta it wraps (consistent); under RawValueMode
  (entered by an outer transport/logical construct via
  withRawTranslationMode) it splices raw — DIVERGING from the
  carrier the motive declares. All observed failures are loud
  (Lean type errors); the audit must establish whether ANY
  instance can elaborate (silent).

## Design question for the audit

What is the correct regime for value content inside transports?
Candidates:
A. Transports at value-domain carriers never enter RawValueMode:
   coerce/Eq.rec with a value-domain (D = Value/VarValue) carrier
   translate their transported value in NORMAL mode and bind at
   the boundary (the IndexArg discipline: error-preserving
   Bind.bind, then raw application under the binder). RawValueMode
   remains for genuinely logical content (proofs, type-level).
   This is D-projection: the carrier's domain decides the value's
   regime — one more projection of classifyDomain, no new mode.
B. Keep RawValueMode but make it consistent: raw-mode TYPE
   translation (motives/annotations inside raw content) emits RAW
   arrows too. Rejected on its face: it forks the type translation
   into modes — the exact dual-representation disease the domain
   map killed; and raw-mode value emission of partial ops loses
   the Except error carrier (soundness).
C. Reject transports whose transported value contains
   phase-beta-requiring content under RawValueMode (loud,
   conservative; the current de-facto state, but as an
   UNDOCUMENTED elaboration failure rather than a named
   translator rejection).

Candidate A is the principled direction (domain-directed, no new
special case); the audit must probe:
1. Every withRawTranslationMode entry point: which are genuinely
   logical (stay raw) vs value transports (switch to A)?
2. The equality-subject rep machinery (standaloneEqualitySubjectRep
   reads PRODUCTION shapes): does switching value content back to
   wrapped production change any subject classification that the
   raw regime relied on (the operand-domain rule is the ONE
   certified-right site — do not regress it)?
3. Eq.rec motive conventions (EqRecConvention) for value carriers:
   does the A regime need a new declared convention field, or do
   the existing wrapped-value conventions cover it?
4. Silent-elaboration hunt: can any carrier/value mode mismatch
   TYPE-CHECK in Lean (e.g. at a monomorphic carrier where raw and
   wrapped coincide)? Any such case is a silent-wrongness
   candidate and a blocker for everything, including the status
   quo.
5. The seq_cong lemma family's Lean-side types: wrapped or raw
   carriers? (The chacha20 Eq.refl mismatch suggests the emitted
   congruence proofs and the carrier types already disagree
   somewhere.)

## Audit verdict (2026-07-18): NEITHER as scoped — design restructured

**The scoping's premise was WRONG and is corrected here.** The two
pinned rows are NOT the same hole and NEITHER is a RawValueMode
seam (all withRawTranslationMode entry points are genuinely
logical; the value-carrying transports translate their values in
AMBIENT mode — value-carrier coerce already implements candidate
A's boundary-bind at Term.hs ~2630).

**Soundness result (probe 6, structural): the status quo is
ALWAYS-LOUD.** Wherever raw and wrapped translations coincide
syntactically, wrapping is the identity (no value-domain content —
nothing to get wrong); wherever they differ, `Except String _` is
never definitionally equal to any `T(tau)` and Lean rejects. This
rests on the DISTINCTNESS INVARIANT — the type translation `T`
never emits an `Except String _`-headed type — which is hereby a
named backstop contract parallel to the Prop backstop: any support
library alias reducing to `Except String _` would reopen the
corner silently.

**The real work, split three ways:**
1. **REV (separate item, NOT transport):** a recursor-post-arg
   raw-function-vs-wrapped-arrow adaptation gap in phase-beta mode
   — the part-3b translateFunctionActualAtConvention path does not
   fire at the failing Num.rec trailing slot even though the same
   natToInt eta-adapts correctly elsewhere in the same file.
   Localize with a fresh instrumented run (suspects: the
   `(Nothing,_)` pass-through gate, or a piFunctionConvention
   classification miss at that motive).
2. **CHACHA (the true transport work):** the FUNCTION-CARRIER
   sub-rule — carrier types + eqProof translate raw-logical; the
   value at its function convention; the coerce needs an emitted,
   checked component-wise congruence at the wrapped components
   (no sound (A -> Except B) -> (A -> B) adapter exists) or a
   named REJECTION. Includes giving the autoEmitRaw combinator
   family (sym/trans/eq_cong/coerce__def/piCong/inverse_eta_rule)
   declared carrier conventions — currently none (Term.hs ~2465
   defers them).
3. **C1-C3 conditions on the surviving parts of A:** transported
   values stay in natural runtime mode (bind at boundary, never a
   mode switch — preserves OP-3 realizations riding inside);
   equality OPERANDS keep the certified operand-domain rule
   untouched; the distinctness invariant documented (above).

## Chacha grounding (2026-07-18, pre-implementation)

The failing `Eq.refl` is emitted by the ONE refl site —
`lowerRawLogicalCallee RawLogicalRefl` (Term.hs ~2392) — for a SAW
`Refl` whose SUBJECT is a TYPE (the seq arrow); the subject's
ambient translation wraps (T of a value Pi = the Except arrow), so
the emitted refl is `@Eq.refl Type (Except…→Except…)` while the
consuming coerce demands `T(A) = T(B)` with `T(A) ≠ T(B)`
syntactically (`Vec (mulNat 4 8) Bool` vs `Vec 4 (Vec 8 Bool)` —
join/split, equal only via the seq_cong lemma family, NOT defeq on
either side).

Investigation entry (next session): dump the SAW-side proof spine
feeding this coerce (which combination of Refl / unsafeAssert /
seq_cong SAW type-checked — SAW-side `mulNat 4 8` reduces, so what
SAW accepted and what T preserves diverge at the join/split
boundary). Then pick the C4 arm:
(a) WRAPPED-COMPONENT CONGRUENCE: keep type-equality subjects at
    T (wrapped) and emit the wrapped-arrow equality from component
    equalities via an emitted support congruence (seq_cong at
    wrapped components — new support lemma family, provable
    generically);
(b) RAW CARRIERS + BOUNDARY ADAPTATION: translate transport
    carriers and proofs raw-logical (T_raw where join/split IS
    defeq or lemma-provable), and adapt the transported VALUE at
    the boundary per candidate A's bind discipline — requires the
    no-sound-(A→Except B)→(A→B)-adapter wall to be respected,
    i.e. only value (non-function) components adapt;
(c) named REJECTION for function-carrier transports whose
    component equality is not defeq under T.
The autoEmitRaw combinator family conventions (audit B3) land with
whichever arm wins.
