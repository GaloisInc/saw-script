# saw-core-lean: external backend review (2026-05-14)

Independent, code-and-doc-level review commissioned to answer four
questions:

1. Is the backend following a clear and coherent strategy?
2. Which parts of the design are clean and well-structured?
3. Of the incomplete parts, which seem stable and well-designed?
4. Are any areas suspicious?

This audit was written without prior involvement in the design and
deliberately distinct from `2026-05-14_wrap-invariant-audit.md`,
which covers a single failure mode (the Phase-β wrap rule) in
depth. The scope here is the whole backend: translator,
specialization pipeline, support library, trust contract, and
recent doc trajectory.

## Material reviewed

- `src/SAWCoreLean/*.hs` (Term, Monad, SpecialTreatment, FixShapes,
  Lean, SAWModule, CryptolModule, plus Language.Lean AST/Pretty)
- `saw-central/src/SAWCentral/Prover/Exporter.hs` for the
  Lean-specific normalization infrastructure
- `lean/CryptolToLean/*.lean` support library
- `doc/architecture.md`, `doc/2026-04-24_soundness-boundaries.md`,
  `doc/2026-05-02_residual-trust.md`, `doc/2026-05-02_recursion-design.md`,
  `doc/archive/2026-05-05_long-term-plan.md`,
  `doc/2026-05-11_beta_replan.md`,
  `doc/2026-05-11_rearchitecting-plan.md`,
  `doc/2026-05-11_target-architecture.md`,
  `doc/2026-05-14_wrap-invariant-audit.md`,
  `doc/getting-started.md`, `doc/contributing.md`
- `otherTests/saw-core-lean/{drivers,proofs,saw-boundary,shape}/`
  inventory; `proofs/*/proof.lean` spot-reads

The Rocq sibling (`saw-core-rocq/`) was used as the structural
reference baseline.

---

## (1) Strategy: coherent intent, recent execution churn

**Intent is clear and right.** The top-level goal — discharge SAW
proof obligations in Lean's kernel by mirroring `saw-core-rocq` —
is consistently named across every file's header comment and every
strategy doc. Module structure, monad shape, treatment-table API,
and entry-point signatures (`writeLean{Term,Prop,CryptolModule}`)
are line-for-line mirrors of the Rocq backend with documented
divergences.

**Execution has iterated four times in nine days.** The trajectory:

| Date | Doc | Stance |
|------|-----|--------|
| 2026-05-05 | `long-term-plan.md` (now archived) | Translator is a near-syntactic rewrite; "future shape-recognizer translator work is presumptively rejected" |
| 2026-05-11 | `rearchitecting-plan.md` + `target-architecture.md` + `beta_replan.md` | Major rebuild: scNormalizeForLean deletion, per-binder fresh universes, Phase-β Except-String wrap as a pervasive transformation |
| 2026-05-14 | `wrap-invariant-audit.md` | Wrap rule "still being audited"; 17/22 proof tests elaborate, 5 remain failing |

The May-5 principle (`long-term-plan.md:57–59`) "shape-recognizer
translator work is presumptively rejected" is **directly inverted**
by `beta_replan.md:204–215`, which introduces an applicative-lift
transformation at every value-level `App` node. The long-term plan
was archived, not retracted; its principle has been quietly
reversed without being marked superseded in the soundness-boundary
and residual-trust docs that pin its consequences.

This is design iteration, not divergence from the goal — but it is
iteration, and the trust documentation has not kept up.

---

## (2) Parts that are clean and well-structured

### `Monad.hs` (289 lines)

Close mirror of `SAWCoreRocq.Monad`. Three additional error
constructors are well-motivated:

- `UnsoundRecursor` — refuses Nat/Pos/Z/AccessibleNat/AccessiblePos
  recursors that would silently swap case order on emission.
- `RejectedPrimitive` — translator-time refusal for shapes outside
  the recognizer's coverage.
- `UnderAppliedMacro` — gate kept for future `n>0` macro entries
  (the current table only uses `n=0`).

Error messages are user-facing paragraph-length diagnostics with
likely causes and workarounds (`Monad.hs:97–243`). This is the
right tone for a tool boundary.

### `Lean.hs`, `SAWModule.hs`, `CryptolModule.hs` (~460 lines combined)

Terse, single-purpose, mirror Rocq exactly. The Cryptol path
threads `globalDeclarations` correctly so subsequent entries don't
re-emit prior bodies inline (`CryptolModule.hs:77`).

### `FixShapes.hs` (190 lines)

Clean shape recognizer. Four shapes:

- `StreamCorec` — `fix (Stream α) (\rec → MkStream α …)`
- `PairStreamCorec` — mutual-stream
- `BoundedVecFold` — `fix (Vec n α) (\rec → gen n α …)`
- Polymorphic stream-iterate (via `classifyPolyStreamIterate`)

Anything else falls through to `RejectedPrimitive`. No silent
rewriting. Recognizer arity contracts are documented and the
recognizer-vs-soundness-argument split (recognize structurally;
trust Cryptol productivity) is honest.

### `SpecialTreatment.hs` table architecture

`defaultTreatmentFor` (line 217) rejects loudly with a documented
reason. No silent passthrough escape hatch. Every unmapped Prelude
primitive must have an explicit `reject "<reason>"` entry,
audited at SAW init via `auditPreludePrimitivesForLean`
(`Exporter.hs:866`). Post-CG-1 (2026-05-07) the previous
`leanIntentionallyUnmappedPrimitives` allow-list was deleted in
favor of explicit reject entries with documented reasons. This is
the right model for a translation boundary.

### `Exporter.hs` normalization infrastructure (saw-central)

- `scNormalizeForLean` (line 554) — iterates SAWCore's
  `scNormalize` with a Lean-specific opaque set.
- `iterateNormalizeToFixedPoint` (line 763) — 100-iter cap, hard
  fail on non-convergence.
- `scLiteralFold` (line 602) — bottom-up constant folding for
  Nat/Int/Bool literal ops; correctly does NOT recurse into
  Pi/Lambda binder types (line 621–633), avoiding the "scLambda:
  variable typing context mismatch" failure mode.
- `discoverNatRecReachers` (line 1014) — auto-derived opaque set
  for defs whose body *directly* contains a Nat/Pos/Z/etc.
  recursor. Crucially does **not** recurse through Constant
  references (line 1041), which would over-conservatively block
  legitimate normalization (regression: test_arithmetic.t11 sext).
- `discoverEnumEncodingReachers` (line 1092) — same pattern for
  the ListSort/FunsTo encoding panic.

Each component has a clear purpose and a pinned regression test
(L-3, L-6, L-14, L-16 lockdown).

### Support library (`lean/CryptolToLean/*.lean`)

The hand-written support library shows the strongest soundness
posture of any layer audited:

- **Exactly 2 `axiom` declarations** in the entire library
  (`SAWCorePrimitives.lean:322, 326`), both Vec↔BitVec round-trip
  identities. Both are decidable at any concrete `n` (a
  ground-`n` proof reduces; only symbolic-`n` proofs depend on
  the axiom). The library uses ~78 defs + ~100 theorems instead.
- **No `sorry` / `admit`** anywhere.
- **No surviving unsound axioms**. The previous
  `error_unrestricted.{u} : (α : Sort (u+1)) → String → α` axiom
  (which produced witnesses of any type, including `Empty`,
  trivially derivable to `False`) was deleted and replaced by
  two distinct error helpers (`SAWCorePrimitives.lean:913–943`):
  - `saw_throw_error` — `Except`-based, propagates visibly.
  - `saw_unreachable_default` — `Inhabited.default` for
    fix-shape lookup-out-of-bounds positions.
- **`saw_unsafeAssert` is a tactic, not an axiom**
  (`SAWCorePrimitives.lean:875–883`). It tries `rfl` → `decide` →
  `simp only [Num_TCNum_inj, Nat_min_self, …]` then retries →
  `omega`. No silent admissions; failure surfaces loudly.
- **Bool case-order correctly permuted**. SAW's `Bool` is
  True-first; Lean's `Bool.rec` is False-first.
  `SAWCorePreludeExtra.lean:42–44` defines `iteDep` with the
  args swapped (`Bool.rec fF fT b`), and `iteDep_True` /
  `iteDep_False` (lines 51, 55) verify the permutation by `rfl`
  at file elaboration.

---

## (3) Incomplete parts that look stable

- **Fix-shape recognizer + lowering**: end-to-end pinned by
  `proofs/recursion_stream_corec/`, `proofs/stream_fibs_corec/`,
  `proofs/E6_popcount/`. Translator-internal soundness has a
  clear argument; residual trust is concentrated on Cryptol
  frontend productivity.
- **Auto-derived opaque set** (`discoverNatRecReachers`): closes
  L-3 cleanly. The textual `leanOpaqueBuiltins` list is retained
  as a sentinel.
- **Translation-time rejections**: every refusal path has a
  regression test cited in `soundness-boundaries.md:47–55`.
- **`SpecialTreatment` reject-by-default model**: post-CG-1 the
  default behavior is loud rejection with a documented reason,
  enforced at audit time. Adding new Prelude primitives without
  a treatment trips the smoketest.
- **DAG sharing**: `translateTermLet` lifts shared subterms into
  nested `let`s (audited 2026-05-06 after Salsa20 ate ~100 GB
  without sharing). Pinned by
  `drivers/cryptol_chained_projection_share/`.

---

## (4) Suspicious areas

These are the items I would push back on.

### 4a. Doc/code drift around `polymorphismResidual`

`architecture.md:35`, `soundness-boundaries.md:49–50`, the
audit-trail in `archive/2026-05-02_post-audit-plan.md:91` and
several other places refer to `polymorphismResidual` as a
translator-time gate that rejects `sort k > 0` binders.

**The function does not exist in the current source.**
`grep -r polymorphismResidual saw-central/src saw-core-lean/src`
returns no hits. The architecture pivoted (per
`rearchitecting-plan.md:128–203` and the current
`Term.hs:250–260`) to per-binder fresh universe variables —
which is a coherent alternative, but it's a different soundness
posture, and the docs still describe the old one.

An auditor reading `soundness-boundaries.md` today believes
`sort k ≥ 1` binders are rejected at translation time. They
aren't. **Either restore the gate or retract the contract.**

### 4b. Phase-β `Except String` wrap is load-bearing without a faithfulness theorem

This overlaps with `wrap-invariant-audit.md` but is worth naming
here as a strategic concern, not just a debugging issue.

The wrap rule has accumulated five carve-outs in successive
audits:

1. Nat at type-index positions: no wrap (`beta_replan.md:64–74`).
2. Motive Lambda binders: no wrap (`Term.hs:1992–2008`).
3. Variable-head types: no wrap (`Term.hs:392–414`).
4. Recursor case-handler binders: no wrap, forced by Lean's
   recursor signature (`Term.hs:1505–1623`).
5. Constructor-arg lambdas: open Q2 in
   `wrap-invariant-audit.md:155–167`; the proposed fix
   (parallel `MkStreamM` / `PairValueM` / `RecordValueM`
   constructors) is exactly the pattern `beta_replan.md:259–261`
   said it would NOT introduce.

**No theorem of the form**

> SAW evaluation of `e` returns value `v` iff Lean evaluation of
> ⟦e⟧ returns `Except.ok v` (modulo a stated mapping)

**is stated anywhere in the docs.** Faithfulness is asserted by
example tests, not by an invariant the translator preserves.
With 5 of 22 proof tests still failing per the latest audit, the
rule is not yet stable.

The wrap rule manifests in `Term.hs` as roughly half its 2,241
lines (≈3× the Rocq sibling). `shouldWrapBinder`,
`isTypeProducing`, `typeArgPositions{,Binders}`,
`translateBindersSelective`, `translateCaseHandler`,
`quantifierShadow`, `isLikelyWrappedTerm`, `buildLifted` are all
wrap-dispatch machinery. The logic is well-commented per call
site but expresses a rule that hasn't been written down.

### 4c. Stale `error_unrestricted` references in proof tests

`SAWCorePrimitives.lean:885–911` documents the deletion of the
unsound `error_unrestricted` axiom. **The following proof files
still reference it on the RHS of their local defs:**

- `proofs/E4_map_id/proof.lean:28, 30`
- `proofs/E5_littleendian/proof.lean:35, 37`
- `proofs/E6_popcount/proof.lean:46`
- `proofs/cryptol_running_sum_eq/proof.lean:31, 34, 38`
- `proofs/popcount32_via_bridge/proof.lean:43, 49–51`

The symbol is not defined anywhere in the library
(`grep -rn '^.*def error_unrestricted\|^.*axiom error_unrestricted'`
returns nothing). These tests almost certainly do not elaborate
today and likely overlap with the "5/22 failing" set named in
`wrap-invariant-audit.md`.

### 4d. Silent error suppression in stream-corec lowerings

`SAWCorePrimitives.lean:196–214` (`cryptolIterateM`) and
`:669–694` (`mkStreamFixM`) fall back to `Inhabited.default` on
per-index `Except.error`, rather than propagating the error.
`wrap-invariant-audit.md:340–353` flags this as a new trust
point: *"`Inhabited` fallback … is a trust point: per-index
errors get silently replaced by `default`."*

This is a real semantic divergence from Cryptol. A productive
Cryptol stream whose body errors at a specific index will
produce `default` in the Lean translation rather than an
observable error. The justification ("Cryptol productivity
guarantees this is unreachable") is the same residual already
used for fix-shape unreachable defaults — but it is a **new
residual-trust item that has not been added to
`residual-trust.md`** (the catalog was last touched 2026-05-02).

Per the project memory entry `project_soundness_absolute.md`,
silent divergence from SAW semantics is exactly the category
that must not exist. Either the trust catalog needs the entry,
or the suppression needs to become explicit propagation.

### 4e. Trust-doc inconsistencies

- **`Bool#rec` direct emission**:
  `soundness-boundaries.md:325–327` marks it comment-grade
  pending L-discipline-3; `residual-trust.md:368–389` marks it
  closed 2026-05-06. Pick one.
- **L-10 universe contract**:
  `soundness-boundaries.md:229–238` and `residual-trust.md:344–361`
  pin "collapse to `Type`"; `rearchitecting-plan.md:444–446` and
  `target-architecture.md:671` say "Replaced by per-binder
  fresh-universe rule." The pinned contract and the planned
  replacement coexist without a superseding mark in the boundary
  docs.
- **Hand-library mirroring rule**:
  `beta_replan.md:259–261` says "No parallel `Cryptol.bvAdd`/etc.
  hand-library mirrors"; `wrap-invariant-audit.md:281–290`
  proposes `MkStreamM`/`PairValueM`/`RecordValueM` parallel
  constructor variants. Same pattern, renamed.

### 4f. `Term.hs` is 3× the Rocq sibling

2,241 lines vs 707 in `SAWCoreRocq.Term`. The bulk is wrap-rule
dispatch (4b). This is the source-level manifestation of the
unfinished design pivot, not a separate concern, but it's worth
recording as a metric: until the line count starts trending
toward the Rocq baseline (or the wrap rule is formalized so the
volume is justified by a stated invariant), the translator is
not "obviously correct by inspection" — the May-5 plan's
stated north star.

---

## Bottom line

**Soundness posture is genuinely strong** for a backend at this
stage of development:

- 2 axioms in the entire support library (both decidable per `n`).
- No `sorry` / `admit`.
- Loud rejection by default at the SpecialTreatment boundary.
- The two largest historical soundness mistakes
  (`error_unrestricted` axiom; universe-polymorphic translation)
  were caught and reversed.
- Rocq mirroring is disciplined.

**Risk is concentrated in the active design pivot.** The Phase-β
wrap pass is too young to have a faithfulness theorem, the docs
lag the code on `polymorphismResidual` and the universe model, a
new silent-divergence trust point (Inhabited fallback) is
uncatalogued, and the latest audit candidly reports 5/22 proofs
still failing.

**The pivot is plausible but unexecuted.** `Except String` is
the right semantic domain for SAW's value-or-error model. The
Prop carve-out is correct. The Rocq-mirror skeleton around it is
sound. But the bet is not yet validated: a written-down
faithfulness invariant, the failing proofs closed without new
carve-outs, the new residuals catalogued, and the docs re-synced
to current code are all required before the wrap rule can be
called stable. If new carve-outs keep accruing while old proofs
stay broken, that's the signal the abstraction doesn't fit.

### Recommended sequence

1. **Re-sync the trust docs to current code.** Remove or
   reinstate the `polymorphismResidual` claim. Mark L-10 as
   replaced. Resolve the Bool#rec direct-emission status
   disagreement. Add the Inhabited-fallback residual to
   `residual-trust.md`.
2. **Write down the wrap-rule invariant.** Even an informal
   statement of "for all SAW terms `e`, ⟦e⟧ in Lean evaluates
   to `Except.ok ⟦v⟧` iff SAW evaluates `e` to `v`" (with the
   five carve-outs explicit) is enough to make new carve-outs
   visible as exceptions rather than implicit additions.
3. **Close or remove the stale `error_unrestricted` proof
   tests.** They are advertising as passing but cannot elaborate
   against the current library.
4. **Then resume Phase-γ work.** Closing the remaining 5 proofs
   without inventing a sixth carve-out is the signal that the
   wrap rule is correct.

If those four steps land cleanly, the architecture holds. If
each invites another design iteration, that's the signal to
reconsider whether `Except String` is the right encoding or
whether a different abstraction (e.g., explicit `Option`-domain
emission, or staged proof-obligation generation à la Rocq's
existential approach) would converge faster.
