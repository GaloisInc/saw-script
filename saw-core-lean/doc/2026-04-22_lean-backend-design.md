# Design: a Lean 4 backend for SAW (mirror of `saw-core-rocq`)

*Draft — 2026-04-22*

## 1. Goal and scope

Build `saw-core-lean`: a SAW backend that translates SAWCore terms to Lean 4
source, structured as a near-mechanical mirror of the existing `saw-core-rocq`
package in `deps/saw-script/saw-core-rocq/`. "Mirror" here is specific — we
reuse the same directory layout, the same command naming pattern, the same
handwritten-vs-generated split for the support library, and the same
"emit-then-check-externally" philosophy. Where Lean differs materially from
Rocq (notably: native `BitVec`, no `coq-bits`, `lake` instead of `opam`,
strict elaboration), we call it out and adapt; we don't reinvent.

Explicit non-goals for the first pass:

- Translating recursive SAWCore terms (`Prelude.fix`). Rocq backend punts
  these as "malformed term"; we punt them the same way. Revisit later with
  Lean's `termination_by` machinery.
- A Lean proof-reconstruction framework ("prove the Cryptol property in Lean
  automatically"). `offline_lean` emits goals as `theorem ... := by sorry`;
  discharging them is out of scope.
- Round-tripping Lean back to SAWCore.
- Anything Cryptol-semantics-level (the dormant `GaloisInc/cryptol-semantics`
  Coq project). That's a different, deeper effort.

## 2. Recap: what the Rocq backend actually does

This is the reference implementation we're shadowing. Key facts, cross-checked
against the live tree:

### 2.1 Directory layout (`deps/saw-script/saw-core-rocq/`)

```
saw-core-rocq/
├── README.md
├── src/                          # Haskell translator
│   ├── Language/
│   └── SAWCoreRocq/
├── saw/
│   └── generate_scaffolding.saw  # regenerates the generated support libs
└── rocq/                         # the support library (Rocq side)
    ├── _RocqProject
    ├── Makefile
    ├── handwritten/CryptolToRocq/   # 10 hand-authored .v files
    │   ├── SAWCoreScaffolding.v
    │   ├── SAWCoreVectorsAsRocqVectors.v
    │   ├── SAWCoreVectorsAsRocqLists.v   # alternative realisation
    │   ├── RocqVectorsExtra.v
    │   ├── SAWCorePrelude_proofs.v
    │   ├── SAWCorePreludeExtra.v
    │   ├── CryptolPrimitivesForSAWCoreExtra.v
    │   ├── SAWCoreBitvectors.v
    │   ├── SAWCoreBitvectorsZifyU64.v
    │   └── Everything.v
    └── generated/CryptolToRocq/     # produced by generate_scaffolding.saw
        ├── SAWCorePrelude.v
        └── CryptolPrimitivesForSAWCore.v
```

The handwritten/generated split matters. Handwritten files bind SAWCore's
primitive types and constants to Rocq-side concepts (e.g. `Bit ↦ bool`,
`Vec n a ↦ Vector n a` with coq-bits backing `BitVector n`). Generated files
are mechanical translations of the SAWCore preludes — re-emitted every time
the SAWCore or Cryptol prelude changes.

### 2.2 SAW-script commands (confirmed via source + `otherTests/saw-core-rocq/`)

| Command | Signature | Purpose |
|---|---|---|
| `write_rocq_term` | `String → [(String,String)] → [String] → String → Term → TopLevel ()` | Emit one SAWCore term as a Rocq `Definition`. Args: `name`, notation remaps, skip list, output path (`""`=stdout), term. |
| `write_rocq_cryptol_module` | `String → String → [(String,String)] → [String] → TopLevel ()` | Translate a whole `.cry` file to a Rocq `Section`. Args: cryptol source, output, remaps, skips. |
| `write_rocq_sawcore_prelude` | `String → [(String,String)] → [String] → TopLevel ()` | Regenerate `SAWCorePrelude.v` from `Prelude.sawcore`. |
| `write_rocq_cryptol_primitives_for_sawcore` | `String → [(String,String)] → [String] → TopLevel ()` | Regenerate `CryptolPrimitivesForSAWCore.v` from `Cryptol.sawcore`. |
| `offline_rocq` | `String → ProofScript ()` | Proof tactic. Dumps the current goal into `{prefix}_prove0.v` (and `_prove1.v`…) with `Definition goal : Prop := …` and a full `CryptolToRocq` preamble. |

The `notations` arg lets a user remap problematic SAWCore operators to custom
Rocq notations; `skips` lets them mark identifiers as "don't translate,
assume the consumer has their own definition." Both are escape hatches we
should reproduce 1:1.

### 2.3 External dependency surface

Rocq 9.1 (core) + stdlib 9.0 + `coq-bits` (for machine-word bitvectors),
installed via `opam`. The support-lib Makefile drives `rocq makefile` →
`Make.rocq`. Users can *read* the emitted `.v` files without compiling
anything; to *typecheck* them they need the full opam install.

## 3. Target architecture: `saw-core-lean`

Same skeleton, Lean 4 flavour.

```
saw-core-lean/
├── README.md
├── saw-core-lean.cabal            # new Haskell package
├── src/
│   ├── Language/
│   │   └── Lean.hs                # Lean 4 surface-syntax AST + pretty
│   └── SAWCoreLean/
│       ├── Translate.hs           # SAWCore Term → Language.Lean AST
│       ├── Monad.hs               # translator state (env, name supply, …)
│       └── Preamble.hs            # imports emitted at top of every file
├── saw/
│   └── generate_scaffolding.saw   # dumps Prelude.lean + Cryptol primitives
└── lean/                          # the Lean-side support library
    ├── lakefile.toml
    ├── lean-toolchain             # pinned to same toolchain as the host project
    └── CryptolToLean/
        ├── SAWCoreScaffolding.lean        (H)
        ├── SAWCoreVectors.lean            (H)
        ├── SAWCoreBitvectors.lean         (H)
        ├── SAWCorePreludeExtra.lean       (H)
        ├── CryptolPrimitivesForSAWCoreExtra.lean  (H)
        ├── SAWCorePrelude.lean            (G)
        └── CryptolPrimitivesForSAWCore.lean (G)
```

(G)enerated, (H)andwritten.

### 3.1 SAW-script commands

| New command | Mirrors |
|---|---|
| `write_lean_term` | `write_rocq_term`, same 5-arg shape |
| `write_lean_cryptol_module` | `write_rocq_cryptol_module` |
| `write_lean_sawcore_prelude` | `write_rocq_sawcore_prelude` |
| `write_lean_cryptol_primitives_for_sawcore` | `write_rocq_cryptol_primitives_for_sawcore` |
| `offline_lean` | `offline_rocq` |

Wiring: extend `deps/saw-script/saw-script/src/SAWScript/Interpreter.hs` the
same way `write_rocq_*` are wired. The actual work lives in a new
`SAWScript/Builtins/Lean.hs` (next to the Rocq one). The emitter is
`SAWCoreLean.Translate`.

### 3.2 `offline_lean` output format

Proposal for the emitted goal file (analog of `invol_prove0.v`):

```lean
import CryptolToLean.SAWCoreScaffolding
import CryptolToLean.SAWCoreVectors
import CryptolToLean.SAWCoreBitvectors
import CryptolToLean.SAWCorePreludeExtra
import CryptolToLean.CryptolPrimitivesForSAWCoreExtra
import CryptolToLean.SAWCorePrelude
import CryptolToLean.CryptolPrimitivesForSAWCore

open CryptolToLean

def goal : Prop := ∀ (xs : Vector (BitVec 8) 4),
  implReverse (implReverse xs) = xs

theorem goal_holds : goal := by
  sorry
```

Two decisions baked in: (a) we emit `Prop` goals, not `Bool`, because the
Cryptol `==` at the property level is meant to be *proved*, not evaluated;
(b) we leave a `sorry` rather than a `by admit` (Lean has both) since `sorry`
surfaces a warning by default, which is what we want.

## 4. Translation table (SAWCore → Lean 4)

The backend is a structural walk over `SAWCore.Term`. Each constructor maps
to a Lean surface form. This table is the entire contract; `saw-core-rocq`'s
analog is the cross-reference.

| SAWCore construct | Rocq emission | Lean 4 emission |
|---|---|---|
| `Sort 0` (the "set of props") | `Prop` | `Prop` |
| `Sort n` (n ≥ 1) | `Type` (with univ poly) | `Type u` (with univ poly) |
| `Bool` | `bool` (from stdlib) | `Bool` |
| `Nat` | `nat` | `Nat` |
| `Integer` | `Z` | `Int` |
| `Vec n a` | `Vector a n` (coq-bits or stdlib, via `SAWCoreVectorsAsRocqVectors`) | `Vector a n` from `Mathlib.Data.Vector` (or std `List.Vector`) |
| `bitvector n` | `coq-bits BITS` | **`BitVec n` — native, no external dep** |
| `Pair a b` | `prod a b` | `a × b` |
| `Eq a x y` | `x = y` | `x = y` |
| `Pi (x : A) B` | `forall (x : A), B` | `(x : A) → B` |
| `Lam (x : A) e` | `fun x : A => e` | `fun (x : A) => e` |
| `App f e` | `f e` | `f e` |
| `Let x = e in b` | `let x := e in b` | `let x := e\n b` |
| Record literal / projection | anonymous `{\| l := v \|}` | anonymous constructor `⟨…⟩` / `.field` |
| `fix` (recursion) | **error: "malformed term"** | **error: same; revisit with `termination_by`** |
| `error` (SAWCore axiom) | rocq axiom | Lean `axiom` or `opaque def … := sorry` |
| String literal | coq `String` | Lean `String` |
| Cryptol sequences (`[n]a` fin) | `Vec n a` via primitives | `Vector a n` via primitives |

The two places this is non-trivial are vector-vs-list (below) and how the
Cryptol prelude is realised. Everything else is local.

## 5. Support-library design

### 5.1 `SAWCoreScaffolding.lean` — base bindings

Direct mirror of the Rocq file. Opens the `CryptolToLean` namespace, binds
`Bit := Bool`, re-exports `Nat`, defines the small SAWCore primitive axioms
(`error`, `unsafeAssert`) as Lean `axiom`s, provides `solveUnsafeAssert` as
a `macro` or `syntax` tactic for discharging the trivial ones.

### 5.2 Vectors — pick one realisation up front

The Rocq backend ships *both* `SAWCoreVectorsAsRocqVectors.v` and
`…AsRocqLists.v` and comments "the latter is a no-go for proofs unless values
are packaged with a proof that their length is equal to the index." We
shouldn't inherit that ambiguity. Recommendation: **go vectors-only**,
backed by `Mathlib.Data.Vector` (or `List.Vector` from std if we want to
avoid mathlib; see §7 open questions). Drop the lists variant entirely.

### 5.3 Bitvectors — the biggest Lean win

Rocq leans on `coq-bits` (`Bits.BITS`, external opam package). Lean 4 has
`BitVec n` in the standard library since 4.7ish, with a rich API
(`BitVec.toNat`, bitwise ops, shifts, comparisons, decidable equality). This
means:

- `SAWCoreBitvectors.lean` is thin — mostly re-exports and a few lemmas.
- Users **do not need** a mathlib-or-external dep just to read/compile
  generated output. They need the Lean toolchain and our support package.
- Word-sized aliases (`U8 := BitVec 8` etc.) live here.

This is worth highlighting because it's the single biggest ergonomic
improvement over the Rocq path.

### 5.4 Generated files

`SAWCorePrelude.lean` and `CryptolPrimitivesForSAWCore.lean` are emitted by
`write_lean_sawcore_prelude` / `write_lean_cryptol_primitives_for_sawcore`,
same as Rocq. They're checked into the repo (like the Rocq ones are) so
end users don't need SAW installed to typecheck generated output.

### 5.5 Build

A normal Lake project in `saw-core-lean/lean/`. No `opam`, no Makefile
driving a second build tool. `lake build` from that directory produces
`.olean` files the user's project depends on. `_RocqProject` equivalent is
`lakefile.toml` + `lean-toolchain`.

## 6. Where Lean differs from Rocq (and why that's fine)

1. **Bitvectors.** Native `BitVec`. Simpler support lib, no external deps.
2. **Install path.** `lake` + `elan` instead of `opam`. Two commands instead
   of five.
3. **Universes.** Both systems have universe polymorphism; the translation
   is 1:1. No new design needed.
4. **Elaboration strictness.** Lean's elaborator is less forgiving than
   Rocq's about implicit arguments and unification. We may need to emit
   explicit `@`-applications more aggressively than the Rocq backend does.
   Action: after the first end-to-end demo works, audit the output with
   `set_option pp.explicit true` and tighten the emitter where the
   elaborator can't figure things out.
5. **Sections vs namespaces.** Rocq `Section` ≈ Lean `namespace`, but
   sections also hoist `Variable` bindings. Cryptol modules translate
   cleanly to namespaces — we lose nothing.
6. **`Admitted` vs `sorry`.** Functionally similar. `sorry` is idiomatic and
   surfaces a warning, which is what we want for `offline_lean`.
7. **Pretty-printing.** The Rocq backend emits verbose output and lets Rocq's
   loader pretty-print it. Lean's printer is less forgiving about parens, so
   the emitter should do a small amount of precedence-aware pretty-printing
   up front. Not a lot — enough to avoid 10-deep paren cascades.

## 7. Phased plan

**Phase 0 — skeleton (1–2 days).** Stand up `saw-core-lean/` with cabal
package, empty `Language.Lean` AST, `SAWCoreLean.Translate` stub that only
handles `Sort`, `Bool`, `Nat`, application, lambda, pi. Wire
`write_lean_term` in the interpreter so it exists as a command even if it
only handles trivial terms. Demo: emit `fun (x : Bool) => x` from a SAWCore
identity term.

**Phase 1 — support lib + primitives (≈1 week).** Hand-write the
`CryptolToLean/` support files (scaffolding, vectors, bitvectors). Enough
that trivial monomorphic Cryptol terms over `[n][8]` translate. Demo:
`reverse.cry`'s `implReverse`{`4, [8]`}` round-trips and compiles.

**Phase 2 — preludes + Cryptol modules (≈2 weeks).** Implement
`write_lean_sawcore_prelude` and
`write_lean_cryptol_primitives_for_sawcore`. Check the generated files in.
Implement `write_lean_cryptol_module`. Demo: the full `reverse.cry` (the
file already in `saw-rocq-example/`) translates and `lake build`s against
the support lib.

**Phase 3 — `offline_lean` and polish (≈1 week).** Proof-script tactic.
Port `otherTests/saw-core-rocq/` to `otherTests/saw-core-lean/` as
regression tests. Document notation remapping and skip lists in the user
manual.

**Phase 4 — release and gaps.** Only now: revisit recursion via
`termination_by`, pretty-printer polish, maybe a `coq-bits`-free path for
generated Rocq by emitting to Lean's `BitVec` as a cross-check.

Rough total to feature parity with the Rocq backend's current state: ~4
weeks of focused work.

## 8. Open questions (decide before Phase 1)

1. **Mathlib or std-only?** `List.Vector` is in std; `Mathlib.Data.Vector`
   has richer API. Generated output will be imported by other people's
   projects, and mathlib is a heavy transitive dep. **Recommend: std-only
   for the core support lib**, put anything mathlib-flavored in a separate
   `CryptolToLean.Mathlib` module users opt into. Needs verification that
   std alone is enough for the Cryptol primitives we need.
2. **Lean toolchain pinning.** The host project is on `v4.30.0-rc2`. Pin
   the support lib to the same toolchain? Or to the last Lean release the
   generated output has been tested against? Leaning toward: pin strictly,
   bump deliberately — track in the lean-toolchain file.
3. **Namespace scheme.** `CryptolToLean` top-level namespace (matches
   `CryptolToRocq`), per-module nested namespace under it? Or flat? Flat is
   simpler; nested mirrors Cryptol's module hierarchy better.
4. **Where to upstream.** Propose to `GaloisInc/saw-script` as a sibling
   directory to `saw-core-rocq`? Or carry out-of-tree here until it's
   proven? Either way the code should be structured so upstreaming is a
   directory move plus a few cabal.project edits.

## 9. What we're not designing yet

- Performance of the translator itself. SAWCore terms can be big; the Rocq
  backend has known verbosity issues. If Lean's elaborator is slower on
  deeply nested terms, we'll find out in Phase 2 and react then.
- Proof-automation reuse. Cryptol has automated provers; none of that
  plumbing crosses the Lean boundary in this design. A future doc can sketch
  `offline_lean`-plus-`simp`-plus-`decide` pipelines.
- A Cryptol-semantics formalisation in Lean (the analog of
  `GaloisInc/cryptol-semantics`). That's a separate, much larger project.

## 10. Success criteria

We consider the backend "done enough to use" when:

- `saw demo.saw` from `saw-rocq-example/` has a `saw-lean-example/` twin
  that produces analogous `.lean` files.
- Those `.lean` files compile with `lake build` against
  `saw-core-lean/lean/`.
- The `offline_lean` output for `reverseInvolutive` elaborates to a
  `theorem ... := by sorry` and the only Lean-side warning is the expected
  `sorry`.
- The emitted `BitVec`-typed code does not require mathlib.

That's the bar. Anything beyond (Lean proof automation, recursive term
support, perf tuning) is Phase 4+.
