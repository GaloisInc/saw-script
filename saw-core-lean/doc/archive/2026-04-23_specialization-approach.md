# Planning note: use-site specialization instead of universe polymorphism

*Draft — 2026-04-23*

Reframe suggested by a Galois conversation: instead of translating the
SAWCore Prelude once as a universe-polymorphic Lean library (which
we've spent significant effort on and still don't have fully
working), translate *exactly what each user program needs*, with
universes aggressively resolved to concrete levels.

This note is a de-risking exercise, not a commitment. Its purpose:
answer "would this actually work, and if so, what's involved" before
we pour more days in.

## 0. The problem we're trying to avoid

We've been trying to produce a Lean file — call it
`SAWCorePrelude.lean` — that is universe-polymorphic and elaborates
once, so user programs import it and instantiate at use sites. That
plan has hit a wall:

- SAWCore is cumulative (`Prop <= Type 0 <= Type 1 <= …`). Lean 4 is
  not. Expressing SAWCore's cumulativity in Lean requires explicit
  `Sort u` universe variables at declaration sites.
- For some Prelude defs (the `coerce` family), multiple `sort 0`
  binders are constrained by an internal `Eq` to be at the same
  universe: needs shared-universe emission.
- For others (the `Pair_fst` / `fst` family), sort-0 binders are
  genuinely independent but their *uses* compose at universes that
  force `u = max 1 u`, which Lean rejects for `u = 0` (Prop).
- A third class (`eitherCong0`) combines both, and no mechanical
  per-def rule appears to satisfy both constraints: hand-patching
  14 defs to shared-universe takes the first failure from line 190
  to line 1584 of the generated 4000+ line file, but defs like
  `eitherCong0` then hit `u =?= max 1 u` and Lean can't solve that
  across two sort occurrences.

External-research-agent's finding: Lean issue #2297 documents that
Lean 4's universe unifier is weaker than Lean 3's exactly around
`max` expressions; the community workaround is `abbrev TypeMax := Type
max u v`, but that's cosmetic cover, not a fundamental fix. Even
with `PLift` wrapping (which the agents explored and rejected for
other reasons), we'd still be inventing a Lean-side encoding of
SAWCore's cumulativity.

## 1. The reframe

User Cryptol programs are *monomorphic at the value level*. When a
user writes

```cryptol
implRev`{4, [8]}
```

the SAWCore translation of that term instantiates `implRev`'s type
parameters `{n, a}` at concrete values `{TCNum 4, [8]}`. The `sort 0`
positions in the SAWCore source of `implRev`'s body are in contexts
where the type argument is now *known*. There's no residual
universe polymorphism to express — every type that was once at
`sort 0` is now concretely `Vec 8 Bool` (or `Bit`, or some other
concrete SAWCore type).

So the Galois suggestion: **don't translate the Prelude once as a
polymorphic library. Translate per user program, with the user's
concrete type arguments beta-reduced into all transitively
referenced Prelude defs, and emit a self-contained Lean file with
fully-resolved universes.**

## 2. Why this is plausible

### 2a. The specialization is what SAWCore semantically means

Beta-reducing a polymorphic def applied to concrete types yields
the *same term* SAWCore would get by unfolding. It's a sound
transformation at the source level — our soundness discipline
(preserve SAW semantics) is trivially met, since we're emitting
exactly what SAWCore's reduction says.

### 2b. The universe pressure disappears

`coerce (Bool) (Vec 8 Bool) eq x` at concrete types — the `Eq (sort
0) Bool (Vec 8 Bool)` translates to `Eq Type Bool (Vec 8 Bool)`,
concretely at Type 0. No universe variables. Lean's unifier has a
trivial job.

The `eitherCong0` residual class we hit today only fails because we
emit it as a universe-polymorphic def that has to satisfy `u = max 1
u` in the abstract. Specialized at a specific type, the `max 1 u`
collapses to a concrete level and the constraint is either
satisfied or a real error (in which case the SAWCore source would
also reject).

### 2c. This is roughly what Rocq does implicitly

Coq's elaborator does universe inference at call sites. When `coerce`
is applied to concrete types in a Rocq-translated user program, Coq
fills in the universes automatically — the polymorphic def on disk
is only *notionally* polymorphic. Our specialization approach is a
more explicit version of that inference, done at translation time
rather than deferred to the target's elaborator.

### 2d. The architecture was already moving this way

Phase-1's "constant body translation" emits referenced Prelude defs
as peer `def`s in the generated output. That's already a limited
form of inlining. Specialization is the same pattern with one
addition: beta-reduce the body against the concrete type arguments
before translating.

## 3. Where it could fail — concrete scenarios

This is the de-risking I want done *before* committing.

### 3a. Polymorphic user terms

A user could write

```saw
let f = {{ specRev }};  // not instantiated
write_lean_term "specRev" [] [] "out.lean" f;
```

Here the SAWCore term carries free type variables. Specialization
has nothing to specialize against. Options:

- **Refuse** with a translator error: require the user to
  instantiate before `write_lean_term`. Reasonable for practical
  Cryptol workflow (users verify concrete properties), but a
  regression from the claim "translator handles arbitrary input."
- **Fall back to universe-polymorphic emission** using the
  existing P4 v2 + hybrid machinery. We know this path has issues
  but most polymorphic defs are simple enough to survive it.
- **Emit via Prop-PLift wrapping** (reviving an earlier rejected
  approach) only for the rare polymorphic case.

Needs investigation: does Cryptol-to-SAWCore translation ever
produce terms with free type variables at `write_lean_term`'s input,
or does Cryptol's own type elaborator always close over them?

### 3b. Recursion through specialization

SAWCore's `Nat__rec` is defined in terms of the native recursor
`Nat#rec`. If a user program calls `Nat__rec` at some concrete
motive `p`, we specialize the body. The body is

```
Nat__rec t x p f1 y pf = Eq#rec1 t x p f1 y pf
```

which references `Eq#rec1` — the native recursor. Translation of
recursors is already handled (Phase 2A emitted `@Foo.rec`).
Specialization doesn't obviously break this, but I haven't probed
it.

Similarly: `Prelude.fix` is rejected at translation. Specialization
doesn't change that rule. Mutual recursion through `let`? Doesn't
appear in SAWCore's prelude as far as I can see; probe to confirm.

### 3c. Output size explosion

Concrete specialization inlines / duplicates. A Prelude def
referenced 20 times from 5 distinct call sites produces 5 distinct
specialized Lean defs. For a real Cryptol crypto spec with heavy
Prelude use, this could blow up badly.

Mitigation: cache specializations by the concrete-arg vector.
SAWCore already hash-cons's terms (`stAppIndex`), so we can use that
hash as the cache key. Two call sites with identical arg-vectors
share one specialized def.

Concrete question: what's the expected specialization count for
`implRev4`? Probably low (tens), but for a real SHA-256 verification
it could be hundreds. Worth estimating.

### 3d. Hidden residual polymorphism

We specialize `implRev` at `{n := TCNum 4, a := Bit}`. The body
references `coerce`, which we then specialize at
`{a := Vec (tcSub n 0) Bit, b := Vec n Bit}`. But `tcSub n 0` —
wait, `n` has been substituted to `TCNum 4`, so `tcSub (TCNum 4) (TCNum
0)` reduces to `TCNum 4`. OK, still concrete.

But what if an *intermediate* Prelude def is genuinely
universe-polymorphic? For instance, `seqMap : (a : isort 0) -> (b :
sort 0) -> (n : Num) -> (a -> b) -> seq n a -> seq n b`. When
specialized at `a := Bit, b := Bit, n := TCNum 4`, those sort
positions resolve. Fine.

More speculatively: a SAWCore typeclass dictionary (e.g.
`PIntegralInteger`) is a record at sort 0, and its fields include
universe-polymorphic functions. Specializing the dictionary at a
concrete user type should concretize those functions too. Probably
works; should verify.

### 3e. SpecialTreatment interaction

Some Prelude names have `mapsTo` treatments (e.g. `Prelude.Eq -> Lean
core Eq`). Under specialization, we don't emit the SAWCore `Eq`'s
body — we emit `@Eq <args>` directly. So `mapsTo` entries still do
what they did. No conflict.

Some have handwritten realizations in `SAWCorePreludeExtra.lean`
(e.g. our `iteDep` wrapper). Under specialization, a user program
referencing `iteDep` at a concrete motive gets `iteDep` called from
our handwritten def. Concrete use is fine; we already made
`iteDep.{u}` universe-polymorphic so any instantiation works.

### 3f. Aggressive universe resolution at concrete level

The plan says "aggressively resolving universe polymorphism." What
does that mean for a `sort 0` occurrence in a specialized body?

Option 1: emit as `Type` (= `Type 0`) — matches SAWCore's sort 0.
Option 2: emit as `Type u` with `u` fresh; let Lean's elaborator
pick.

Option 1 is simpler and honest: if specialization succeeded, every
sort-0 position is genuinely at sort 0, no polymorphism needed.
Option 2 is safer in edge cases but defeats the point.

Go with Option 1 by default, but detect cases where a body has a
residual type-variable (e.g. if the user's Cryptol is itself
polymorphic) and back off to polymorphism for those only.

## 4. Staged de-risking plan

Before any translator changes, do the following investigations.

### Stage 1 (read-only, ~2h)

Enumerate the SAWCore constants that `implRev4` transitively
references. For each, record:
- Is it a pure primitive (axiom / no body)?
- Is it defined? If so, what free type variables does its body have?
- At what concrete arguments does `implRev4` call it?

This builds a dependency tree and tells us the scale: is it tens of
defs, or hundreds?

Tool: SAWCore has `scSharedTermSearchNames` or similar — walk
`implRev4`'s body. Use `scTypeOf` at each `Constant` node to record
its type.

### Stage 2 (hand-specialization, ~half day)

Produce, by hand, a self-contained Lean file for `implRev4` with all
Prelude references inlined at concrete types. Does it elaborate?

This is the single biggest de-risk. If it works, the translator
change is mechanical. If it doesn't, we learn *why* before spending
a day on implementation.

### Stage 3 (translator sketch, ~half day)

Write `translateConstant`'s specialization path in enough detail to
see how it plugs into the existing code. Don't commit yet. Sketch
the caching scheme; estimate output size on `implRev4`.

### Stage 4 (implementation + validation, 1-2 days)

Implement. Run `demo.saw` end-to-end. Verify all four outputs
elaborate under `lake env lean`.

## 5. Implementation sketch (not committed)

In `SAWCoreLean.Term`:

```haskell
-- Replace (or augment) the current translateConstant that emits
-- the body polymorphically with:
translateConstantApp ::
  TermTranslationMonad m => Ident -> [Term] -> m Lean.Term
translateConstantApp i args = do
  -- Consult SpecialTreatment as before; only fall through to
  -- specialization for defs with DefPreserve / UsePreserve.
  treatment <- findSpecialTreatment i
  case atUseSite treatment of
    UseMacro _ _ -> ... -- as today
    UseRename _ _ _ -> ... -- as today
    UsePreserve -> do
      mm <- view sawModuleMap <$> askTR
      case resolveNameInMap mm i of
        Just (ResolvedDef d)
          | Just body <- defBody d -> do
              sc <- askSc  -- new: state passes SharedContext through
              specialized <- liftIO $ scApplyAll sc body args
              reduced <- liftIO $ scWhnf sc specialized
              -- Or scBetaReduceFully for a more aggressive reduce
              emitOrReuseSpecializedDef i args reduced
        _ -> ... -- axiom / primitive: emit reference as today
```

The `emitOrReuseSpecializedDef` helper caches by a hash of the
reduced term. On first call for a given (ident, args) combination,
it translates the reduced term and pushes a new peer def onto
`topLevelDeclarations`. Subsequent calls with matching hash reuse
the emitted Lean ident.

Name mangling: `implRev_spec_abc123` (where `abc123` is a short
hash) or `implRev__v1`, `implRev__v2` sequentially. Either works.

### Things I'd want to preserve from current translator

- **Everything in `Language.Lean.AST`, `Language.Lean.Pretty`** —
  no changes needed. The output is still Lean 4 syntax.
- **SpecialTreatment table and its combinators** — still used, just
  for the subset of defs that map to Lean core (Eq, Bool, Unit,
  etc.). Specialization only happens for defs without a treatment.
- **SAWModule / CryptolModule walkers** — still used for
  `write_lean_sawcore_prelude` (demoted to "reference dump, not
  expected to elaborate") and `write_lean_cryptol_module` (user
  modules still translate via the module walker; per-def
  specialization happens inside).
- **Interpreter wiring, offline_lean, existing demo** — all
  unchanged. The user-facing commands are the same.

### Things I'd demote or remove

- **The P4 v2 universe-polymorphism machinery** (universe lists on
  Decl, Sort variants `SortVar`/`SortMax1Var`/`SortMax1Vars`) stays
  in the AST but gets exercised only on genuinely-polymorphic input
  (Stage 3a's "polymorphic user term" case). For typical concrete
  input, the emitted defs have no universe lists.
- **The expectation that the auto-translated SAWCorePrelude.lean
  elaborates** — becomes "reference output, expected to have
  impedance issues; not on the critical path."
- **My P6a/P6b investigation work** — lives on the WIP branch as
  reference but isn't imported into main.

## 6. What this changes about past commitments

### The soundness doc (2026-04-22_soundness.md)

Specialization is *more* sound than polymorphic emission in one
respect: it produces Lean output whose semantics is exactly what
SAWCore would reduce to at the user's concrete instantiation. The
polymorphic approach always risked subtle cumulativity-gap issues
(`Prop` at a `Type` position silently working via some Lean
coercion). Specialization removes that risk class entirely.

Doc update needed: add "specialization" as the primary translation
strategy; frame polymorphic emission as a fallback for the rare
polymorphic-user-term case.

### The P6 investigation docs

The two existing P6 docs (investigation, v2 status) remain valid as
records of what we tried. They should stay as reference — the
failure modes they document are real and would resurface if we ever
tried polymorphic emission again.

### The audit agent's findings

Still valid; most of the audit's A-class items (A1 Inhabited, A2 Eq
explicit, A5 pretty-wrapping) apply equally to specialized output.
The universe-polymorphism findings become less central.

## 7. What I'd need to verify before proceeding

**Blocker-class unknowns** — if any of these is "no," specialization
isn't viable:

1. **Does SAWCore provide a `scBetaReduce` or equivalent that works
   on shared terms?** If not, we'd have to roll our own, which is a
   significant detour.
2. **Does specialization actually terminate on Prelude defs?** If
   some defs are transitively cyclic (recursion through mutual
   reference), specialization could loop. We'd need a fixed-point
   bound or a cycle detector.
3. **Does the hand-specialized `implRev4` elaborate?** Stage 2.

**Scale-class unknowns** — if any of these is "big," specialization
is unattractive but not blocked:

4. How many specialized peer defs does a typical `implRev4` require?
5. How many distinct specializations does a typical Cryptol crypto
   spec require (heuristic ≤ 500 for verification to be practical)?

**Interaction unknowns** — probably fine but worth checking:

6. Do the Phase-1 Inhabited-instance injections interact with
   specialization? (I think yes — specialized Inhabited instances
   for the concrete type.)
7. Does `offline_lean` interact correctly? (The goal term is a
   `Prop`; its proof-term structure specializes similarly.)

## 8. Honest tradeoffs

### Pro

- Sidesteps the universe-polymorphism impedance entirely for
  concrete user programs.
- Semantically transparent — the output is what SAWCore reduction
  would compute.
- Removes months of Phase-2+ work from the critical path for actual
  users who just want to prove things about their concrete Cryptol.
- Rocq-style implicit specialization, made explicit.

### Con

- More per-program output. A Prelude def referenced by 20 user
  programs produces 20 specialized copies across their files. For
  shared libraries / reuse across Lean projects, this is ugly.
- Requires a beta-reduction pass at translation time. We're now
  doing real type-checking work, not just syntactic translation.
- Doesn't handle polymorphic user input gracefully (§3a).
- Abandons an entire line of investigation (P4 v2 universe poly,
  P6/P6v2 classification) that we invested significant time in.
  It's not wasted — those docs catalog what Lean 4 can and can't
  do, which is valuable — but it's emotionally a pivot.

### Neutral

- Changes the definition of "done" for the translator. Previously:
  emit a reusable polymorphic Lean library that mirrors the full
  SAWCore Prelude. Now: emit self-contained Lean files for user
  programs. Both are legitimate goals; the user workflow for the
  Cryptol-verification use case is essentially identical.

## 9. Decision points

Before implementing:

### D1. Do we commit to specialization as the primary strategy?

My recommendation: yes, but only after Stage 1–2 investigation
succeeds. If Stage 2 (hand-specialization of `implRev4`) fails, we
learn why and iterate on the plan.

### D2. What's the policy for polymorphic user terms?

Options:
- (a) Refuse, force user to instantiate
- (b) Fall back to polymorphic emission (current P4 v2 behavior)

My recommendation: (b) for now, since we have the machinery;
refactor to (a) if the fall-back proves buggy or if we want a
stricter contract.

### D3. Do we keep `write_lean_sawcore_prelude` as a command?

Yes: it's useful for inspecting what SAWCore says, even if the
output doesn't elaborate in Lean. Redocument as "reference dump."
Low cost.

### D4. Do we preserve the P6a WIP branch?

Yes. It's a record of what we tried. If specialization fails at
Stage 2 and we return to polymorphic emission, the WIP branch is
our starting point for "try again with more sophistication."

## 10. Recommendation

1. Execute Stage 1 (dependency enumeration for `implRev4`) today.
   2h investment, read-only, produces a concrete answer to "how big
   is the specialized output."
2. Execute Stage 2 (hand-specialization of `implRev4`) next. Half a
   day. If it elaborates, we have high confidence specialization
   works for our driving use case.
3. Write a follow-up planning note after Stage 2 with concrete
   numbers and specific risks validated or refuted.
4. **Only then** commit to Stage 3-4 implementation.

If this note looks reasonable, I'd want to proceed with Stage 1
first. Stage 1's output will itself be a commit-worthy artifact
(a dependency analysis doc) that informs whether to proceed.

## 11. Open questions for the user

Before I start Stage 1:

1. Is "it works for `implRev4` but fails for some hypothetical
   polymorphic Cryptol term" an acceptable outcome, or should the
   translator handle both?
2. If output size is a concern (Stage 3c), do you have a budget —
   e.g. "<1000 lines for a typical Cryptol spec"?
3. Any guidance on naming? `implRev_spec_abc123` vs `implRev__v1`
   vs `implRev#4` — I'll default to a human-readable scheme but
   would want to know if you prefer a specific style.
4. Should the auto-translated SAWCorePrelude.lean continue to be
   maintained (as a reference artifact) or dropped entirely? I'd
   keep it as reference but it's debatable.
