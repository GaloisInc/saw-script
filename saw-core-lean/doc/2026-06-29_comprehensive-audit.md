# Comprehensive Lean Backend Audit

Date: 2026-06-29

This audit treats the current Lean backend as untrusted code. The target is a
sound SAW proof-discharge backend that matches or exceeds the Rocq backend
without moving semantic trust into Haskell. Four independent review passes
covered proof checking, Haskell emission architecture, Rocq parity and coverage,
and Lean support-library semantics. This note records the findings after local
validation.

## Executive Summary

The project is converging in the right direction: the old direct fix-shape
helper surface is gone, generic `fix` and stream construction are now
proof-carrying, imported constants no longer silently fall back to bare names,
and completed proof outlines are tied to generated goals.

The audit also found two concrete support-library semantic bugs that must be
fixed before broader architecture cleanup:

1. Bitvector division by zero does not match SAW semantics.
2. `bvLg2` implements floor log, while SAW implements ceiling log for nonzero
   values.

The other major findings are mostly known trust-boundary items: `offline_lean`
is still an exporter that reports SAW proof success before Lean replay, emitted
outline files may contain local `by sorry` obligations, and two Vec/BitVec
coherence axioms remain in the Lean support library.

## P0 Findings

### `bvUDiv` / `bvSDiv` zero-divisor semantics are wrong

SAW's Prelude specifies zero-divisor behavior:

- `bvUDiv x 0` returns all bits set.
- `bvURem x 0` returns the dividend.
- `bvSDiv x 0` returns all bits set for non-negative dividends and `-1` for
  negative dividends.
- `bvSRem x 0` returns the dividend.

References:

- `saw-core/prelude/Prelude.sawcore:1836`
- `saw-core/prelude/Prelude.sawcore:1846`
- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:399`
- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:404`
- `otherTests/saw-core-lean/drivers/arithmetic/test_arithmetic.t2.lean.good:9`

The Lean support library delegates directly to `BitVec.udiv`, `BitVec.umod`,
`BitVec.sdiv`, and `BitVec.srem`. In the pinned Lean toolchain,
`(5 : BitVec 8).udiv 0` evaluates to `0`, not `255`. `umod` and `srem` return
the dividend for the checked positive case, but division is definitely wrong.

Impact: generated Lean can prove a different bitvector division theorem from
the SAW obligation.

Next action: define SAW-specific division wrappers with explicit zero-divisor
branches. Add focused tests for unsigned division by zero, unsigned remainder by
zero, signed positive and negative division by zero, and signed remainder by
zero.

### `bvLg2` is floor-log, but SAW computes ceiling-log

SAW's concrete primitive computes:

```haskell
bvLg2 (BV m x) = BV m (if d > 0 then k+1 else k)
  where (k, d) = lg2rem x
```

This is `ceil(log2 x)` for nonzero inputs, with `0` mapped to `0`.

References:

- `saw-core/src/SAWCore/Prim.hs:342`
- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:484`

The Lean support library currently uses `Nat.log2 (vecToBitVec v).toNat`, which
is floor-log. For example, SAW gives `bvLg2 3 = 2`, while Lean's current
definition gives `1`.

Impact: any emitted term using `bvLg2` can have the wrong meaning.

Next action: implement SAW's convention, e.g. `if x = 0 then 0 else
Nat.log2 (x - 1) + 1`, then add driver/proof coverage for powers of two,
non-powers of two, and zero.

## P1 Findings

### `offline_lean` is still emit-and-admit

`offline_lean` writes a Lean file and returns `SolveSuccess` to SAW without
invoking Lean. The emitted file intentionally contains a `theorem goal_holds :
goal := by sorry` stub.

References:

- `saw-central/src/SAWCentral/Builtins.hs:1355`
- `saw-central/src/SAWCentral/Builtins.hs:1393`
- `saw-core-lean/src/SAWCoreLean/Lean.hs:100`
- `saw-script/src/SAWScript/Interpreter.hs:5279`

This mirrors the Rocq offline-exporter shape, but it is not yet the desired
Lean proof-discharge backend. The final backend needs either:

- an emit-only command that does not solve the SAW goal, plus a replay command,
  or
- a checked `offline_lean` mode that invokes the pinned Lean toolchain and only
  returns success after checking the exact generated obligation.

Prototype status: acceptable only if documented as emit-stage behavior and not
counted as checked discharge.

### Generated outlines contain local `by sorry` obligations

Proof-carrying lowerings currently emit local proof placeholders as
`Lean.Tactic "sorry"`.

References:

- `saw-core-lean/src/SAWCoreLean/Term.hs:1257`
- `saw-core-lean/src/SAWCoreLean/Term.hs:1280`
- `saw-core-lean/src/SAWCoreLean/Term.hs:1320`
- `saw-core-lean/src/SAWCoreLean/Term.hs:1352`
- `saw-core-lean/src/SAWCoreLean/Term.hs:1850`

This is sound only as an incomplete outline format. A completed proof artifact
must have no residual `sorryAx`, and no SAW command should accept such a file as
a proof.

Next action: keep current outline emission for prototype ergonomics, but classify
driver tests containing local `sorry` as open-obligation tests. Design the
external obligation format so completed artifacts provide named evidence rather
than editing trusted definitions in place.

### The Lean support library still has two nonstandard axioms

The only live Lean axioms are the Vec/BitVec round-trip claims:

- `vecToBitVec_bitVecToVec`
- `bitVecToVec_vecToBitVec`

References:

- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:338`
- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:342`
- `otherTests/saw-core-lean/support/lean-proof-test.sh:176`

They are plausible and much narrower than the earlier bitvector axiom surface,
but final soundness should not allow nonstandard support-library axioms.

Next action: prove them in Lean and remove the proof-harness allowlist.

### Raw Lean injection bypasses the support-library boundary

`SAWModule.translateDecl` emits `InjectCodeDecl "Lean"` verbatim.

Reference:

- `saw-core-lean/src/SAWCoreLean/SAWModule.hs:172`

This bypasses the generic primitive/axiom rejection policy and can smuggle
arbitrary Lean declarations into generated module output if the SAWCore module
is untrusted.

Next action: reject `InjectCodeDecl "Lean"` in the sound backend path, or treat
it as an explicitly trusted support-library mechanism unavailable to ordinary
translation.

### Haskell-side literal folding changes the theorem before Lean sees it

`scNormalizeForLean` runs `scLiteralFold`, which evaluates selected Nat, Int,
Bool, and `ite`/`iteDep` forms in Haskell before translation.

References:

- `saw-central/src/SAWCentral/Prover/Exporter.hs:555`
- `saw-central/src/SAWCentral/Prover/Exporter.hs:573`
- `saw-central/src/SAWCentral/Prover/Exporter.hs:639`
- `saw-central/src/SAWCentral/Prover/Exporter.hs:707`

The rules are intended to mirror SAW evaluation, but they violate the current
"Haskell stays dumb" policy. A wrong fold changes the proposition Lean proves.

Next action: either remove the pass from trusted emission or make it
proof-carrying: emit the literal term plus a Lean equality proof/obligation for
the simplified form.

### Imported realizations are type-checked, not semantically proved

Explicit imported realizations now emit `__saw_realizes_*` aliases at the
translated SAW type, which is an improvement over bare-name fallback. However,
the alias only checks that the Lean target has the expected type; it does not
prove that the target implements the intended source meaning.

References:

- `saw-core-lean/src/SAWCoreLean/Term.hs:1887`
- `saw-core-lean/src/SAWCoreLean/Term.hs:1901`
- `saw-core-lean/src/SAWCoreLean/Term.hs:1937`

Next action: decide whether imported realization type-checking is an explicit
trusted boundary for Rocq parity, or require a Lean realization theorem/witness
for each imported constant.

## P2 Findings

### Raw/wrapped adaptation still relies on transitional Haskell classifiers

The design has moved away from Lean AST recognition, but Haskell still contains
substantial shape policy:

- `shouldWrapBinder`
- `typeArgPositions`
- `natValueResult`
- `phaseBetaResultShape`
- `skipBinderWrap`
- `inRecursorCaseBinder`

References:

- `saw-core-lean/src/SAWCoreLean/Term.hs:573`
- `saw-core-lean/src/SAWCoreLean/Term.hs:613`
- `saw-core-lean/src/SAWCoreLean/Term.hs:1124`
- `saw-core-lean/src/SAWCoreLean/Term.hs:1134`

These are now the main architecture debt. They are not all wrong, but they are
still an implicit semantic model in Haskell.

Next action: proceed with the explicit `ExpectedShape` / `RawReason` /
`CalleeConvention` refactor once the P0 semantic bugs are fixed.

### Sort literal translation may over-generalize

The code distinguishes binder-position and value-position sorts, but ordinary
`FTermF (Sort ...)` translation currently uses `BinderPos`.

References:

- `saw-core-lean/src/SAWCoreLean/Term.hs:292`
- `saw-core-lean/src/SAWCoreLean/Term.hs:2481`

Potential impact: explicit SAW sort literals may be generalized to fresh Lean
universes where concrete levels should be preserved.

Next action: add focused tests before changing this path, then thread
`SortContext` through term translation if the test exposes real drift.

### Driver tests need clearer classification

The driver harness elaborates generated files, but elaboration accepts `sorry`.
This is useful for emission-shape coverage, not proof-discharge coverage.

References:

- `otherTests/saw-core-lean/support/lean-driver-test.sh:90`
- `otherTests/saw-core-lean/support/lean-elaborate.sh:100`
- `otherTests/saw-core-lean/support/lean-proof-test.sh:29`

Next action: classify tests as:

- emission/golden only,
- elaborates with open obligations,
- checked discharge.

Only checked-discharge tests should count toward proof-backend soundness.

### Proof harness is strong enough for trusted regressions, not product replay

The proof harness now checks generated-goal drift for completed outlines and
audits theorem axioms. However, its harness-added checks use unqualified names
inside the user's proof file context.

Reference:

- `otherTests/saw-core-lean/support/lean-proof-test.sh:342`

A malicious proof file could keep a namespace open and make appended unqualified
checks refer to local `goal` / `goal_closed`. This is acceptable for trusted
regression fixtures, but not for a product proof checker.

Next action: product replay should generate a separate checker file that refers
to fully qualified, fresh obligation names.

### Documentation and examples lag current behavior

Several docs still describe future or historical behavior as if it were current.
Examples include `offline_lean` behavior, proof-cookbook tactic names, and stale
README links.

References:

- `saw-core-lean/doc/getting-started.md:28`
- `saw-core-lean/doc/proof-cookbook.md:210`
- `saw-core-lean/README.md:70`

Next action: after the P0 semantic fixes, do a docs scrub that clearly
separates current behavior, intended final behavior, and archived planning
notes.

## Lower-Priority / Needs Confirmation

### `genM` / `atWithDefaultM` strictness

The support library eagerly sequences vectors. An audit pass flagged that this
could expose errors in unused elements if SAW/Cryptol semantics are demand
driven for these positions.

References:

- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:583`
- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:590`
- `saw-core-lean/lean/CryptolToLean/SAWCorePrimitives.lean:538`

This needs a semantics check before changing code. The current eager behavior
may be correct for SAWCore value evaluation under the backend's `Except`
translation, but it should be justified explicitly.

## Recommended Priority Order

1. Fix `bvUDiv` / `bvSDiv` / zero-divisor semantics and add focused tests.
2. Fix `bvLg2` semantics and add focused tests.
3. Replace or prove the Vec/BitVec round-trip axioms.
4. Decide the external obligation format for definitions containing local
   proof obligations; classify driver tests accordingly.
5. Decide the `offline_lean` emit-only vs checked-replay command split.
6. Remove or make proof-carrying the remaining Haskell semantic routing:
   `scLiteralFold`, raw Lean injection, imported realization contracts, and
   transitional raw/wrapped classifiers.
