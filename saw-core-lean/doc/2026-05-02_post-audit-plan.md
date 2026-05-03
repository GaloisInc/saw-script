# Post-audit long-term plan

*2026-05-02 — supersedes the §3-§4 plan in `2026-05-01_status-and-next-steps.md`.*

Three audits ran today (`doc/audit/2026-05-02_*.md`): soundness +
Rocq parity, test coverage + Cryptol surface gaps, usefulness +
docs + quality. Findings cross-cut the previous Arc 1-4 framing,
so this doc reframes the work as **seven phases**, ordered for
lowest cost / highest leverage first. Each phase has concrete exit
criteria. The Arc 4.3 / 4.4 / 4.5 items survive as Phases 5, 6, 7.

## Cross-cutting findings

The audits agree on three things:

1. **Translator core is solid in the parts that are tested,
   but the audit's severity ranking is the wrong bar.** ~1700 LoC,
   high-quality code, three pinned-failure intTests for the named
   boundaries. The audit rated several soundness gaps as
   low/medium because of containment arguments ("not translator-
   reachable today", "rare in practice"). **We're throwing out
   that ranking.** Comments-as-guarantees are not acceptable —
   any soundness claim that rests on code review or "we don't
   currently emit this shape" is a future hole. Every feasibly-
   killable gap moves to the top of the queue (Phase 1a below).
2. **The output is hard to *use*.** Emitted goals are walls of
   `Bool.rec` over axiomatic `bvAdd`/`bvEq`/etc. — neither
   `decide` nor `simp` can fire. There's no walkthrough showing
   how to discharge an `offline_lean` goal end-to-end. So the
   practical value today is "verify SAWCore terms elaborate as
   Lean", not "prove Cryptol properties in Lean".
3. **Test coverage is thinner than the status doc claims.** Rocq
   parity is 11/13 — *better* than the doc's "9 unmirrored". But
   negative-path coverage is bad: 0/7 `TranslationError`
   constructors in smoketest, only `UnsoundRecursor` in intTests.
   No CI integration at all. Two real coverage gaps inside
   the existing tests (`test_records` record-update battery,
   `test_sequences` comprehension/transpose) we haven't flagged.

Plus a fourth, tactical: **documentation has accreted** — 19 dated
files, no consolidated as-of-today reference, `saw-lean-example/README.md`
still says "Phase 0", `saw-core-lean/.tmp/` has 4845 lines of stale
P4 cruft.

## Soundness as the bar

The driving principle: **kill every soundness gap that can
feasibly be killed**, then make the remaining boundary load-
bearing — tested, not commented. Specifically:

1. **No comment-grade guarantees.** "Translator never emits this"
   or "rare in Cryptol practice" doesn't count. If a gap is real
   in the type theory, it's real.
2. **Every soundness claim pins a regression test.** A claim
   without a test that *would catch* its violation is a future
   hole.
3. **Hand-maintained safety lists are last resorts, not first
   choices.** `leanOpaqueBuiltins`, identifier-collision avoidance,
   `SpecialTreatment` completeness — anywhere we can replace a
   list with auto-derivation, we do.
4. **Loud failure beats silent containment.** A gate that's
   bypassed today by accident-of-emission-shape is not a gate.

The Phase 1a catalog below operationalizes this. Each item is a
specific gap, what closing it looks like, and the test that pins
it closed.

## Phased plan

### Phase 1a — Soundness lockdown *(1-2 weeks)*

Highest priority. No subsequent phase ships before this is done.
Every item ships as a closed-loop "code change + pinned
regression test"; the soundness-boundaries doc gets updated to
cite test paths rather than rationales.

#### Lockdown catalog

**L-1. `polymorphismResidual` catches every `sort k>0` binder.**
*Maps to audit S-1.* Currently walks outer pi-spine via `asPiList`;
nested binders inside argument types slip through. Work: full
term-tree traversal at the type level, plus a smoketest pair
(positive: `(a : Type) → a → a` accepted; negative: nested
`(f : (α : sort 1) → β) → γ` rejected). Fuzz over deeply-nested
shapes if practical.

**L-2. `unsafeAssert` axiom shape matches SAW exactly.** *Maps to
audit S-2.* Tighten Lean-side from `Sort u` to `Sort (u+1)`
parallel with `error`. Pinned regression: a Lean file that tries
to instantiate at `Prop` fails elaboration. Drops the "translator
never emits this" containment argument entirely — the axiom shape
itself is the gate.

**L-3. Auto-derive opacity for every unsound recursor type.**
*Maps to audit S-3.* Extend `discoverNatRecReachers` to scan for
`Z#rec`, `AccessibleNat#rec`, `AccessiblePos#rec` (and any other
recursor whose Lean realisation lacks an equivalence proof).
Shrink `leanOpaqueBuiltins` to the irreducible residue
(`subNZ`/`ZtoNat`-style structural wrappers). Pinned: smoketest
asserting the auto-derive set covers a representative term per
recursor type.

**L-4. `Vec` constructor and recursor not reachable from user
proofs.** *Maps to audit S-4.* Currently `Vec n α := Vector α n`
exposes `Vector.mk` / `Vector.rec` to anyone importing the
support library. Choose: (a) redefine `Vec` as an opaque
`structure` with a smart-constructor API surface, sealing
`.mk`/`.rec`; or (b) module-export discipline that prevents the
constructors from being reachable from outside. Pinned regression:
a Lean file that pattern-matches on `Vector.mk` fails to compile
against the support library.

**L-5. `fix` rejected at the SAW translation boundary, not at
Lean elaboration.** *Maps to audit S-5.* Explicit `SpecialTreatment`
entry for `fix` and `fix_unfold` that throws `TranslationError`.
Loud at SAW time, matching the doc's claim. Pinned: existing
regression test moves from "fails at `lake env lean`" to "fails at
`writeLeanTerm`".

**L-6. `scNormalize` fixed-point cap fails loud, not silent.** A
synthetic test that constructs a term whose normalization doesn't
converge within 100 iterations and confirms `TranslationError`
surfaces (not a silent return of the partially-normalized term).

**L-7. `iteDep` / `ite` case-permutation pinned at the Haskell
side.** Currently `rfl`-proven on the Lean side. Add a Haskell
smoketest that emits both shapes through `Term.hs` and confirms
the rfl-equivalence still holds — so a regression in emission
order is caught at `cabal test` time, not at `lake env lean`.

**L-8. `coerce` axiom shape positive regression test.** Currently
"matches SAW's `(a b : sort 0)` by code review." Pinned smoketest
that emits a `coerce` use and asserts the axiom signature; a
broader-universe regression must fail typecheck.

**L-9. `@`-prefix on emitted constructor and recursor heads
pinned.** Currently enforced in `Term.hs:315-318` and `:602-603`;
a regression that drops the prefix could silently mis-apply
positional vs implicit arguments. Smoketest emitting a
constructor and a recursor and asserting the `@` is present.

**L-10. `translateSort` universe-collapse contract pinned.**
Single point of trust: every non-Prop sort collapses to `Type 0`.
Add a positive test that the collapse never weakens an emitted
theorem's semantics, and document the contract in the soundness
doc as the *primary* trust assumption (currently it's barely
mentioned).

**L-11. `escapeIdent` identifier safety exercised.** The
Z-encoding path is dead from a test perspective (Audit B). A SAW
name that lands on a Lean keyword (`for`, `match`, `theorem`,
…) or a built-in identifier could shadow and cause misapplication.
Smoketest covering: non-`[A-Za-z0-9_']` characters, every Lean
keyword as a SAW identifier, and identifiers colliding with
imported names from `CryptolToLean.SAWCorePrimitives`.

**L-12. `writeLeanCryptolModule` passes through every soundness
gate.** Trace the code path. `writeLeanTerm` and `writeLeanProp`
both invoke `polymorphismResidual`; confirm the module-walk path
does too, and that no module-emitter shortcut bypasses any
declared gate. Pin a regression: a Cryptol module containing a
gating shape (polymorphic-over-Type def) is rejected at
`write_lean_cryptol_module` time, not just at later
`write_lean_term` calls.

**L-13. Every boundary in `2026-04-24_soundness-boundaries.md`
pins a regression test.** Currently 3 of 7 are pinned
(`UnsoundRecursor`, `polymorphismResidual`, `error_prop`). Write
the missing 4: `coerce` shape, `unsafeAssert` shape (post-L-2),
`iteDep` permutation (post-L-7), `Vec` opacity (post-L-4). Update
the doc to cite test paths instead of rationales.

**L-14. Auto-detect missing `SpecialTreatment` entries at
translator startup.** Walk the Prelude and Cryptol-prelude module
maps at translator init; warn or throw on names reachable from
common emission paths that have no `SpecialTreatment` and no
realisation in the support library. Converts the "fails mid-Lean-
elaboration with unknown identifier" failure mode (fail-closed but
opaque) into a startup-time diagnostic with a concrete name to
add. Pinned: synthetic missing-name test confirms the diagnostic
fires.

**L-15. Soundness audit runs as a CI job.** A scripted check that
enumerates the lockdown catalog and confirms each item still has a
linked test. Catches regressions in the *catalog* itself.

**L-16. `Bool#rec` doesn't surface bare in translated output.**
*Mid-flight discovery, not in the original 16-item plan — found
analyzing `test_offline_lean.t4`.* SAW's Bool ctor declaration is
True-first (`True; False`) so the auto-generated `Bool#rec` arg
order is `(motive, trueCase, falseCase, scrutinee)`. Lean's
`Bool.rec` is False-first — order `(motive, falseCase, trueCase,
scrutinee)`. Pre-L-16, `scNormalize` was unfolding the
`iteDep`/`ite` wrappers down to bare `Bool#rec1`, and the
translator emitted `@Bool.rec` with args in SAW's order — Lean
read the second arg as `falseCase`, silently SWAPPING branches at
every `if`/`then`/`else` translation. Every existing test
output passed elaboration despite being semantically wrong. The
fix: keep `iteDep`, `ite`, `iteDep_True`, `iteDep_False`, and
`ite_eq_iteDep` in `leanOpaqueBuiltins` so `scNormalize` doesn't
unfold them; the surface stays at the wrapper level and routes
via SpecialTreatment to the L-7-permuted Lean wrappers. Pinned
by smoketest "Bool#rec doesn't surface bare in translated output"
plus the absence of `Bool.rec` in any `.lean.good` post-fix.

The L-16 lesson: **textual pinning + Lean elaboration ≠ semantic
correctness**. A swap of cases produces type-correct output that
elaborates fine but is semantically wrong. Phase 3 closes this
gap by adding semantic-verification tests (proofs that discharge
translated Cryptol properties) — see
`2026-05-02_semantic-testing-investigation.md`.

#### Phase 1a exit criteria

- Every L-* item closed in code with a pinned test.
- `2026-04-24_soundness-boundaries.md` rewritten to cite test
  paths rather than narrative rationales; the catalog above
  becomes its appendix.
- A short follow-up doc — `doc/2026-05-XX_residual-trust.md` —
  enumerates whatever residual trust remains (e.g., the SAWCore
  `Prelude.sawcore` axioms we transport, the `unsafeAssert`
  primitive, the `coerce` axiom). What's left should be
  *exactly* the assumptions inherited from SAW — nothing the
  Lean backend introduces of its own.

### Phase 1b — Hygiene + CI *(2-3 days)*

Deferred from the original Phase 1; runs after the lockdown.

- Wire `saw-core-lean-tests` and `saw-core-lean-smoketest` into
  `.github/workflows/ci.yml`. `lean-elaborate.sh` already
  returns 77 on missing lake.
- Delete `saw-core-lean/.tmp/`, empty
  `saw-core-lean/lean/intTestsProbe/`.
- Update `saw-lean-example/` — re-run `demo.saw`, recommit
  `out/`, fix README phase-numbering.

**Exit criteria.** CI runs both Cabal stanzas plus the lockdown
job from L-15; example output is current; no checked-out cruft.

### Phase 2 — Usefulness foundation *(1-2 weeks)*

The single biggest perception change for the project.

- **First-proof walkthrough.** `doc/getting-started.md`. Take
  `test_offline_lean.t1_prove0.lean`, set up a Lake project,
  walk through closing the goal (or getting close before `sorry`,
  with the gap explained). One real worked example beats ten
  design docs.
- **`@[simp]` lemmas in the support library** for `Bool.rec` on
  literals, `iteDep_True`/`iteDep_False` (already `rfl`-proven —
  just attribute them). Moves dozens of common sub-goals from
  intractable to reducible.
- **Error-message polish.** `UnsoundRecursor` and
  `polymorphismResidual` currently address contributors, not
  Cryptol users. One sentence per error explaining what to do
  Cryptol-side.
- **Pretty-printer indentation.** `Pretty.hs:170-173`'s `App`
  rule compounds at depth — `saw-lean-example/out/` shows lines
  reaching column 700+. Worth a focused fix.

**Exit criteria.** A new user can read `getting-started.md`,
emit one of the existing test goals, open it in a Lake project,
and discharge it (perhaps with a planted `simp` set).

### Phase 3 — Test coverage hardening *(3-5 days)*

Defensive, mostly mechanical.

- **`TranslationError` battery.** One synthetic Term per
  constructor in `SmokeTest.hs` (currently only `UnsoundRecursor`
  is exercised, via intTests).
- **`polymorphismResidual` positive battery.** Three smoketests
  confirming `Type → α → α`, `Nat → ...`, `Num → ...` are NOT
  rejected. Pairs with the existing negative case.
- **`escapeIdent` smoketest.** The Z-encoding path is dead from
  a test perspective.
- **Slice tests for popcount + salsa20-quarterround.** Drop in
  `test_cryptol_module_popcount.saw` and
  `test_cryptol_module_salsa20_q.saw`. Either they pass
  (confirming the exercises clean-elaborate) or they surface
  primitive gaps. Highest-value test addition — converts "we
  think exercises/ would partially work" into ground truth.
- **Backfill `test_records` t8-t15** (record-update battery)
  and **`test_sequences` comprehension/transpose** if the
  primitives they need can be enumerated. If they need new
  primitives, route into Phase 6.

**Exit criteria.** Every `TranslationError` constructor pinned;
`exercises/` translation status known concretely.

### Phase 4 — Documentation consolidation *(2-3 days)*

- **`doc/architecture.md`** — current as-of-today reference.
- **`doc/primitives-reference.md`** — table of every
  `SpecialTreatment` entry, what SAWCore name it routes from,
  what Lean target it routes to, what realisation lives in the
  support library.
- **`doc/contributing.md`** — "how to add a new Cryptol
  primitive", "how to extend the soundness boundary".
- **`doc/archive/`** — move 2026-04-22 / 2026-04-23 / 2026-04-24
  / 2026-05-01 dated trajectory docs there. Keep the as-of-today
  files at top-level.
- **README** — gain a "Getting started → Reference →
  Contributing" structure.

**Exit criteria.** New contributor or user can find what they
need without reading chronologically.

### Phase 5 — Recursion design *(was Arc 4.4)*

The big unblocker for real Cryptol coverage. **Doc first**:
`doc/2026-05-XX_recursion-design.md` surveys the three plausible
emit targets — `partial def` everywhere, pattern-recognized
bounded `fix`-as-fold, true corecursion via `Stream.corec` —
recommends an ordering, and breaks the implementation into
sub-tasks. Implementation is at least a week after the doc lands.

**Exit criteria.** Design doc accepted; the deferred
`test_cryptol_module_sha512.saw` functor test drops in once the
chosen path is implemented.

### Phase 6 — Cryptol surface expansion *(was Arc 4.5)*

Fill primitives as demos surface. **Hard rule under the lockdown
principle**: no new primitive lands without (a) a realisation
whose shape exactly matches its SAW counterpart and (b) a pinned
regression test that exercises the routing.

- L-14's startup detection (from Phase 1a) catches missing
  entries before they become Lean elaboration errors.
- **Auto-derive (or partially auto-derive) `SpecialTreatment.hs`**
  from a Prelude module-map walk — same shape as Phase 1a's
  expanded `discoverNatRecReachers`.
- **Per-demo additions**: head/tail/zip/scanl, `ecFromTo`/
  `ecTranspose`, IntMod/Rational/Float for ECC code paths. Each
  goes through the lockdown bar: matched-shape realisation +
  pinned routing test.

**Exit criteria.** `dump_lean_residual_primitives` emits empty
on the demo set we care about; new demos fail loudly with an
actionable message; the `SpecialTreatment` table grows with no
soundness regressions.

### Phase 7 — Proof-side tooling *(was Arc 4.3)*

Depends on Phase 2. Once `getting-started.md` exists, the
next question is whether we ship a proof library — `simp` sets,
helper tactics, BitVec-binding decisions — or punt that to
downstream users. **Doc first**, possibly a separate project.

**Exit criteria.** Decision documented: own the proof side, or
ship clean primitives and let users build their own machinery.

## Open strategic questions

These don't fit the phase ordering — they need explicit decisions
before they can be planned:

- **`translateSAWModule`?** (Audit A P-1.) Specialization design
  intentionally sidesteps full module emission, but the
  capability gap blocks "audit the SAW Prelude as Lean" workflows.
  Defer until a concrete user materialises.
- **Native `Lean.BitVec` binding?** (Audit C, plus
  `2026-05-01_bitvec-binding-decision.md`.) Multi-week. Can't
  evaluate cost/benefit until Phase 3 establishes which
  exercises actually translate. Re-evaluate after Phase 3.
- **Upstream destination?** (Status doc §2 flags as TBD.)
  Stays open until the project hits "useful for someone".

## Suggested ordering

**Phase 1a is gating.** Nothing else ships until the lockdown
catalog is closed. Estimated 1-2 weeks; the upper bound is
honest, not aspirational — L-1, L-4, and L-12 each have real
design content.

After 1a: 1b (hygiene + CI) → 2 (usefulness foundation) → 3
(test coverage) → 4 (doc consolidation), in linear order
(~3 weeks). Then Phase 5 (recursion design — multi-week), at
which point Phase 6 expands organically under the lockdown
discipline and Phase 7's "do we own the proof side?" question is
informed by Phase 2's walkthrough.

The bar throughout: **after Phase 1a, the only residual trust
the Lean backend introduces beyond SAW's own axiomatic primitives
should be precisely cataloged in `doc/2026-05-XX_residual-trust.md`**.
Anything not in that catalog is a regression.
