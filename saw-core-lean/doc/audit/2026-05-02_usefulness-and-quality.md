# Usefulness + Docs + Quality Audit
*2026-05-02*

## Summary

- **Translator is correct on what it accepts but the output is currently
  unusable as a proof artifact on anything non-trivial.** Every Cryptol
  primitive resolves to a Lean `axiom`; `Bool.rec` walls appear in the goals.
  No `decide` / `native_decide` / `simp` story — `by sorry` is the expected
  end state today, not a starting point.
- **No user-facing documentation walks anyone from `offline_lean "g" goal;`
  to a single discharged theorem.** Existing docs are contributor-facing
  trajectory (Phase 0..4, parked branches, audit memos), not a "discharge
  your first goal" tutorial.
- **`doc/` is 19 dated design files; no consolidated as-of-today
  reference.** Newcomers must read chronologically to know which earlier
  claims have been superseded — exactly the cost the README warns about.
- **Code quality is high**: ~1700 LoC, heavily commented, every non-obvious
  decision points at a doc; three pinned-failure intTests cover the
  soundness boundaries. `SpecialTreatment.hs` is hand-curated and will not
  scale to real Cryptol without auto-generation.
- **No CI integration.** `.github/workflows/ci.yml` contains zero
  references to "lean"; `saw-core-lean-smoketest` and `saw-core-lean-tests`
  are wired into Cabal but never run by GitHub Actions.

## Usefulness findings

### End-to-end story today

`offline_lean "g" goal;` produces a file like
`otherTests/saw-core-lean/test_offline_lean.t1_prove0.lean`:

```
import CryptolToLean
open CryptolToLean.SAWCorePrimitives
noncomputable def goal : Prop :=
  (x y : Vec 8 Bool) -> @Eq Bool
    (@Bool.rec (fun (_ : Bool) => Bool)
       (bvEq 8 (bvAdd 8 x y) (bvAdd 8 x x))
       Bool.true (bvEq 8 x y))
    Bool.true
theorem goal_holds : goal := by sorry
```

To use it, a user needs to (a) drop the file into a Lake project with
`CryptolToLean` on the library path — undocumented; users either copy
into `saw-core-lean/lean/` or roll their own Lake project with a
path dep — and (b) discharge the `sorry`. (b) is where it falls apart:
all bv ops are `axiom` (`SAWCorePrimitives.lean:171-214`), int ops too
(`131-141`), so `decide`/`native_decide` cannot fire and `simp [bvAdd]`
does nothing. `if`/`&&`/`||` come out as `@Bool.rec (fun (_ : Bool) => …) … b`
(see `test_offline_lean.t2_prove0.lean`); `simp` doesn't unfold `Bool.rec`
without help. Nothing in the repo demonstrates closing one of these goals.

So today's answer to "what can a user do end-to-end?" is: **verify
SAWCore terms elaborate as Lean** (via `lake env lean`). That's a real
soundness check on the translator, but it isn't a proof artifact.

### Gaps for productive use

- **No "first proof" walkthrough.** Even a 30-line worked example
  (Cryptol prop → file → `unfold Bool.rec; cases b <;> rfl` or similar)
  would change the perception from "infrastructure demo" to "useful tool".
- **Bitvector ops are opaque axioms.** Until the most common bv ops
  reduce — even partially, even via a compromise binding — nontrivial
  properties are intractable Lean-side. The largest single load-bearing
  item for "useful". Status doc Arc 3 already parks this.
- **No `@[simp]` reduction lemmas in the support library.** Every
  translated `if` lands as `Bool.rec`; lemmas like `Bool.rec_true`/
  `Bool.rec_false` and `@[simp]` on `iteDep_True`/`iteDep_False`
  (already proven `rfl` at `SAWCorePreludeExtra.lean:45-50`) would let
  `simp` chip in. None exist today.
- **Pretty-printer indentation is awful at depth.** `Pretty.hs:170-173`
  uses `group $ hang 2 $ fillSep` for `App`; nested calls compound. In
  `saw-lean-example/out/invol_prove0.lean` lines reach column 700+. Output
  is correct but unreadable.
- **`saw-lean-example/out/` is stale** — emitted before the `open
  CryptolToLean.SAWCorePrimitives` change; bare qualifications make it
  uglier than current output.
- **Error messages are translator-author-facing.** `UnsoundRecursor`
  (`Monad.hs:68-75`) tells a Cryptol user to "Add the referring
  definition to leanOpaqueBuiltins (in SAWCentral.Prover.Exporter)" —
  actionable for a contributor, opaque for a SAW user.
  `polymorphismResidual` (`Exporter.hs:797-802`) points at an on-disk doc
  path. A "what to do as a Cryptol user" sentence would help in both.
- **`make test` works** from `otherTests/saw-core-lean/`, but the README
  doesn't mention it — it only references higher-level `cabal test`.

## Documentation findings

### Strong

- **`doc/2026-04-24_soundness-boundaries.md`** is the single best
  document — clear "what we guarantee", "what users must not do", a
  failure-mode table. Exemplary; other docs should aim here.
- **README accurately reflects status** post-pivot.
- **Lean-side support library docstrings** (`SAWCorePrimitives.lean`,
  `SAWCorePreludeExtra.lean`, `SAWCoreBitvectors.lean`) are exemplary —
  every axiom explains the SAWCore source, the soundness rationale, and
  pointers upstream.
- **`Term.hs` and `SpecialTreatment.hs` are heavily commented**, with
  every non-obvious decision citing a stage commit or audit doc.

### Stale / missing

- **No "getting started" path.** README jumps Status → Layout → Demo →
  Tests → Documentation; nothing walks "Cryptol module → translation →
  usable Lean".
- **No primitive-table reference.** `SpecialTreatment.hs` *is* the
  reference, but contributors adding (e.g.) `signedBvDiv` must read
  ~360 lines to find the right pattern.
- **No TOC / index for `doc/`.** README §"Documentation" lists "read in
  chronological order; the trajectory itself is part of the
  documentation". Status doc itself recommends consolidation; not done.
- **`doc/2026-04-22_soundness.md` is stale** (status doc lines 96-97
  flags it: "predates the specialization pivot; some statements ('the
  prelude is the unit of trust') are no longer load-bearing"). Not
  reconciled.
- **`saw-lean-example/README.md` is severely stale** — lines 19-32
  describe Phase 0 output and call `write_rocq_cryptol_module` "Phase 2".
  All three primitives ship and work today.
- **No upstreaming or contributor docs.** No "how to add a new Cryptol
  primitive" guide; no "where to upstream" decision (status doc §2
  flags as TBD).
- **`saw-core-lean/.tmp/` contains 4845 lines of stale `SAWCorePrelude.lean`
  + `sawprelude_errors.txt` from Apr 22** (parked P4 attempt artifacts).
  Properly gitignored by root rule, but checked-out cruft confuses
  newcomers.
- **`saw-core-lean/lean/intTestsProbe/` is empty.** Either delete or
  document.

## Code/quality findings

### Perf

- `scNormalizeForLean` 100-iter cap is a safety net (`Exporter.hs:556-568`);
  real workloads reach fp in 1-2 iters. `Rev.lean` (4109 lines) elaborates
  fine. Reasonable.
- Term-sharing memoised on `termIndex` in `discoverNatRecReachers`
  (`Exporter.hs:653-700`) and `collectConstantNames`. No quadratic
  blow-up.
- `leanOpaqueBuiltins` lookup is O(N) per name (`Exporter.hs:619`); fine
  at ~30 entries, should be a `Set` if it doubles.
- Pretty-printer indentation compounds with nesting — readable for
  small terms, unusable past depth ~10.

### Maintainability

- **`SpecialTreatment.hs` is hand-curated** (~80 entries). Status doc
  Arc 3 proposes auto-deriving `leanOpaqueBuiltins` by walking the
  Prelude ModuleMap; the same pass could partially generate
  SpecialTreatment or at minimum diagnose missing entries at startup.
  Today, every new Cryptol primitive surfacing in a demo is a manual
  `SpecialTreatment.hs` edit + a manual axiom in `SAWCorePrimitives.lean`.
- **`UseMacroOrVar` fallback is subtle** — `NatPos`-as-`id`
  (`SpecialTreatment.hs:368-372`) is correct but readers don't obviously
  see why under-applied uses get `id` and applied uses collapse.
- **`mkDefinitionWith` strips lambda type annotations when the
  signature supplies them** (`Term.hs:454-477`); right but only the
  comment explains why. No regression test pins this.
- **`Lean.AST.hs` exports a wildcard** (`{-# OPTIONS_GHC
  -Wno-missing-export-lists #-}`); compare `Pretty.hs` which lists
  `prettyDecl` only. Tightening AST exports is hygiene work.

### Build hygiene / CI

- **No `.gitignore` under `saw-core-lean/`.** Root `.gitignore` covers
  `.lake/`, `.tmp/`, `dist-newstyle`, `build.log` — sufficient. OK.
- **`saw-core-lean/lean/.lake/`** correctly gitignored.
- **No CI workflow runs Lean tests.** Cabal stanzas at
  `saw.cabal:349-362` and `1162-1181` are unwired in
  `.github/workflows/ci.yml`. Status doc §2 already flags this.
- **`saw-core-lean/lean/intTestsProbe/`** empty; delete.
- **Lean toolchain pinned to `leanprover/lean4:v4.29.1`** with no
  upgrade path documented; bumping requires a manual edit + rebuild.

### Other

- **No native `Lean.BitVec` binding.** `bitvector n := Vec n Bool`
  (`SAWCoreBitvectors.lean:31`). Cuts off most of Lean's bv tactical
  machinery (`bv_decide`, `BitVec.toNat` rewrites). Documented in
  `doc/2026-05-01_bitvec-binding-decision.md` as intentionally punted.
  Single biggest "useful for proofs" gap.
- **`error.{u}` uses `Sort (u+1)`** (excludes `Prop`); tested via
  `intTests/test_lean_soundness_error_prop`. Good.
- **`unsafeAssert.{u}` allows `Sort u` including `Prop`**
  (`SAWCorePrimitives.lean:255`). A Lean-side user could in principle
  write `unsafeAssert Prop True False` and derive inconsistency. The
  boundary is documented in soundness-boundaries.md but not statically
  enforced — the largest "soundness rests on user discipline"
  knife-edge in the project.
- **`UnderAppliedMacro` is the only `TranslationError` constructor with
  no test.** Smoketest gap noted in status doc.
- **No threading/IO concerns.** Translator is pure aside from the
  IO `scNormalize` callback at the boundary; output goes through
  `writeFile` directly.

## Recommendations

Prioritized by daily-workability impact:

1. **Write a "discharge-your-first-goal" walkthrough** —
   `doc/getting-started.md` with one of the simpler
   `test_offline_lean.tN_prove0.lean` files, Lake project setup,
   imports, a closed proof (or a proof that gets close before sorry,
   with a clear explanation of where it stops). Highest ROI;
   single biggest perception change.
2. **Add `@[simp]` reduction lemmas** to the support library for
   `Bool.rec` on literals, `iteDep_True`/`iteDep_False`. Already
   proven `rfl`; just attribute additions. Moves dozens of common
   sub-goals from intractable to reducible.
3. **Consolidate `doc/`** into a maintained as-of-today set
   (`architecture.md`, `primitives-reference.md`, `contributing.md`)
   with the dated trajectory moved to `doc/archive/`.
4. **Wire smoketest + intTests into a CI matrix entry.** Without it,
   pinned references are only as good as local `make good` runs.
5. **Improve user-facing wording on `UnsoundRecursor` and
   `polymorphismResidual`** — add a "what to do as a Cryptol user"
   sentence.
6. **Update `saw-lean-example/`** — re-run `demo.saw`, recommit `out/`,
   fix the README's stale Phase-numbering.
7. **Address the `unsafeAssert` Prop knife-edge** — tighten to
   `Sort (u+1)` like `error`, or static-check no emitted code applies
   it at `Prop`.
8. **Auto-detect missing `SpecialTreatment` entries at translator
   startup** so a new demo fails fast with an actionable message
   rather than a mid-file Lean elaboration error.
