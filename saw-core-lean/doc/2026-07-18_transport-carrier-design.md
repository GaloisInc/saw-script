# Value content inside equality transports (the transport corner)

2026-07-18. Status: IMPLEMENTED 2026-07-19 (the mode-uniform
type-subject spine convention below landed as designed —
Convention.hs/Term.hs; rev.cry reduced module emits). Originally:
SCOPING — pre-audit. The LAST rev.cry blocker
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

## Investigation result (2026-07-19): the spine dumped

The pre-implementation description above is CORRECTED by the dump.
The failing emission (Emitted.lean:282, compressed) is:

    coerce (Except String (Vec (mulNat 4 8) Bool)
              -> Except String (Vec 4 (Vec 8 Bool)))   -- T(T1)
           (Except String (Vec (mulNat 8 4) Bool)
              -> Except String (Vec 4 (Vec 8 Bool)))   -- T(T2)
           (@Eq.rec Type (Vec 32 Bool)
              (fun y' eq' =>
                 (Vec (mulNat 4 8) Bool -> Vec 4 (Vec 8 Bool))
                   = (y' -> Vec 4 (Vec 8 Bool)))       -- motive RAW
              (@Eq.refl Type (Except String ...
                 -> Except String ...))                -- base WRAPPED
              (Vec 32 Bool)
              (@Eq.rec Num x__' ...))                  -- Num index proof
           (fun (v : Except String (Vec (mulNat 4 8) Bool)) => ...)

Corrections to the grounding note above:
- There is NO join/split wall here. The coerce is between two arrow
  types differing only in DOMAIN INDEX ARITHMETIC (`mulNat 4 8` vs
  `mulNat 8 4`); both domains are Lean-defeq to `Vec 32 Bool`
  (mulNat reduces on literals). The codomain `Vec 4 (Vec 8 Bool)`
  is shared.
- The consumer is not "a coerce rejecting a refl": the coerce
  lowering (Term.hs ~2613) already translates carriers AND proof in
  ambient mode and applies the coerced function directly (the
  function-carrier arm emits; no reject). The loud failure is
  INSIDE the proof spine, at the standalone Eq__rec lowering.
- The SAW proof is an inlined Eq__rec congruence spine at a SORT
  carrier (a = sort 0; the subjects are TYPES), with a nested
  Num-carrier Eq__rec (value-subject, all non-arrow content) and an
  unsafeAssert leaf (obligation `Eq Num x__' x__'`, closed by rfl).

The defect, precisely: for a TYPE-SUBJECT spine the standalone
lowering mixes two type interpretations. Subjects and branch
translate in AMBIENT mode (`translateTermWithShape` before the
convention is chosen; adaptTo-raw is the identity on their raw
shapes), so the branch Refl's subject comes out at T — the WRAPPED
arrow. The motive and eqProof are FORCED RAW
(`MotiveComputesRawType` -> `withRawTranslationMode`), so the same
SAW arrow type comes out RAW inside the motive. `Eq.rec` demands
the base inhabit `motive x rfl` — wrapped refl vs raw motive, loud.

## Design (2026-07-19): type-subject spines are MODE-UNIFORM

Rule (calculus §Raw Logical Callees, new sub-case): when the
equality carrier `a` is a SORT — the subjects are TYPES, D-decided
by `asSort`, never by operand production shapes — the declared
subject representation is the CURRENT MODE's type translation
(T in ambient Phase-β content; the raw translation inside raw
logical mode, where the two coincide by construction). EVERY field
of the convention follows the same mode: subjects, motive
(plain `translateTerm`, no mode flip), branch, nested proof.

Why this is the right thing (not arm (a), (b), or (c)):
- A type-level congruence spine is PARAMETRIC in the type
  interpretation: Eq__rec/Refl/sym/trans steps prove the image
  equality verbatim whichever interpretation the embedded types are
  read at. The CONSUMER fixes the interpretation: a value transport
  (coerce) moves a value inhabiting T(T1) and needs `T(T1) = T(T2)`
  — so ambient spines read types at T. Raw logical content (lemma
  bodies auto-emitted under raw mode) reads them raw — unchanged,
  since inside `withRawTranslationMode` current-mode = raw.
- Leaves re-check at the chosen images: a Refl leaf needs the
  T-images Lean-defeq (here: mulNat literal reduction — holds); an
  unsafeAssert leaf emits its obligation AT the images. Where SAW
  accepted a conversion that T does not preserve, elaboration or
  the obligation fails LOUDLY. No silent divergence: the emitted
  proof is checked by Lean's kernel end to end.
- No new support lemmas (arm a unnecessary — the SAW spine already
  IS the congruence proof; we only read its types at T), no
  boundary adapter (arm b unnecessary — the value already inhabits
  T(T1) natively), no rejection (arm c unnecessary).

Value-subject conventions (carrier NOT a sort) are unchanged
byte-for-byte: raw subjects keep the forced-raw motive (the legacy
corpus), runtime subjects the wrapped motive, function subjects
Slice 5c. The type-subject case bypasses
`standaloneEqualitySubjectRep` entirely — D decides from the
carrier, not from shapes (types happen to carry raw shapes, but the
declared rule must not depend on that accident).

Implementation surface:
- `EqualitySubjectTypeImage` constructor on `EqualitySubjectRep`
  (Convention.hs), documented as above.
- `MotiveComputesTypeImage` arm on `MotiveResultMode`:
  `translateEqRecMotiveAtConvention` translates the motive with
  plain `translateTerm` (current mode).
- `eqRecConventionForStandalone` gains the `asSort aArg` test FIRST;
  subjects/branch at `ExpectRaw RawTypePosition` (they are types;
  adaptTo chokepoint preserved), proof in current mode, result
  `BindingRaw`.
- `RawLogicalEq` / `RawLogicalRefl` at sort carriers reclassify to
  the same rep — emission-identical today (their subjects already
  translate ambient), but the production record and trace become
  truthful rather than mode-coincidental.
- The autoEmitRaw combinator family (sym/trans/eq_cong/coerce__def)
  stays UsePreserve: the lemmas are PARAMETRIC in their carriers,
  so ambient call sites instantiate them at T-images with no
  per-name behavior. KNOWN RESIDUAL: arrow-FORMING combinators
  called by name (piCong family) state raw arrows in their
  auto-emitted signatures; an ambient call feeding a T-consumer
  would mismatch LOUDLY. No pinned row exercises this; extend when
  one does.

Audit questions (adversarial, pre-implementation):
1. Nested VALUE-subject spines inside an ambient type-subject proof
   (the Num Eq__rec): their subjects are type-INDEX values. Under
   ambient translation do Num variables/ctor applications carry raw
   production shapes (rep stays raw, emission unchanged), or can a
   shape flip the inner convention to runtime-subject (wrong-motive
   garbage — loud, or silent)?
2. Regression surface: any GREEN emission with an ambient
   type-subject Eq__rec today elaborated only because its content
   was all non-arrow (raw = T images coincide). Is the new emission
   byte-identical there (index values inside types translate raw in
   both modes)?
3. unsafeAssert at SORT carriers inside ambient spines: the
   obligation becomes `T(T1) = T(T2)` (possibly wrapped arrows).
   Confirm the obligation machinery states it at the images and
   that provability = component provability (congruence), never a
   vacuous or unstatable goal.
4. Soundness: can reading SAW's proof at T-images ever PROVE an
   equality whose SAW counterpart did not hold semantically
   (T-image conflation)? (Claim: no — Lean checks the transported
   spine independently; coercion along a Lean-proved equality of
   Lean types is unconditionally sound in Lean, and SAW-side
   falsity surfaces as an unprovable obligation.)
5. The reclassification of Eq/Refl at sort carriers: confirm
   emission-identical (no green-row byte diffs) and that no
   consumer keyed on the OLD rep value for type subjects.

## Audit verdict (2026-07-19): SAFE-WITH-CONDITIONS

No new silent-unsoundness path; every divergence the design
introduces is loud (compile-time exhaustive enums, or Lean-kernel
via the distinctness invariant). The mechanic fixes the pinned row.
Per-question results (evidence in the audit record):

- Q1 CORRECTED: nested Num/Nat index spines stay raw for TYPE-LEVEL
  indices (Num vars read Γ raw records; TCNum-of-literals and
  mulNat are raw producers). A VALUE-COMPUTED index (TCNum of a
  bvToNat-style wrapped computation) flips the nested spine to the
  runtime-subject convention — which then fails LOUDLY at the outer
  type-spine boundary (distinctness invariant), never silently. No
  pinned row produces one.
- Q2: regression surface is structurally EMPTY — ambient and raw
  type translation differ only where wrapExcept fires (value-domain
  Pis, incl. function fields nested in tuple/record/Stream
  type-subjects), and any type-subject spine carrying such content
  is red today with exactly the known-gap failure. The only live
  ambient `Eq.rec Type` in the corpus is the chacha row itself.
- Q3: unsafeAssert at sort carriers states its obligation at the
  ambient images (operands translate ambient in
  translateUnsafeAssertObligation); false assertions are unprovable
  obligations, loud.
- Q4: no new conflation — Except is an injective type constructor,
  so reading at wrapped images never identifies more than raw;
  residual assumptions (T value-injectivity, Lean defeq vs SAW
  convertibility) are pre-existing to every coerce.
- Q5: Eq/Refl reclassification is emission-identical (subjects
  already translated ambient; carrier of a bare sort is
  mode-independent; no consumer branches on the rep value beyond
  the projection functions).
- Q6: ambient motive translation keeps the type-producing lambda
  structural; `y' -> C` wraps via the kind-directed DVarValue rule
  — exactly the T-images the branch and the coerce demand.
- Q7: all enum consumers are exhaustive without silent defaults,
  EXCEPT subjectCarrierAt's wildcard second clause — condition 2.

Binding conditions (all implemented 2026-07-19):
1. Distinctness invariant gains a support-library guard: smoketest
   lint "support library defines no Except-headed type alias".
2. Explicit TypeImage arms at every consumer (subjectCarrier,
   subjectCarrierAt BEFORE the wildcard, subjectTerm, the eqProof
   case, translateEqRecMotiveAtConvention,
   eqRecConventionForStandalone); classification via the shared
   `subjectRepForCarrier` (asSort test, D-decided).
3. Q1 rationale corrected as above (flip is loud, not "unchanged").
4. Full differential corpus run required before commit.
5. Efficacy: mulNat is `@[reducible] def mulNat := Nat.mul` and the
   nat-literal macros are reducible defs, so literal index
   arithmetic is kernel-defeq — confirmed in
   SAWCorePrimitives.lean; the row run is the empirical check.
6. piCong/arrow-forming named combinators stay a KNOWN LOUD
   residual (raw-arrow signatures vs ambient T-consumers); no green
   row instantiates one at an ambient T-consumer today.
