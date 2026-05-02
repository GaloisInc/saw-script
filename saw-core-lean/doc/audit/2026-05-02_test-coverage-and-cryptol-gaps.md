# Test Coverage + Cryptol Surface Gaps Audit
*2026-05-02*

## Summary
- Rocq parity is **far better than the 2026-05-01 status doc claims**: of 13 Rocq drivers, the Lean side mirrors 11. Only `test_cryptol_primitives`, `test_prelude`, and `test_cryptol_module_sha512` remain unmirrored, each for a deliberate reason.
- The primitive table covers `Prelude.sawcore` reasonably well (~70 of ~108 primitives) but only **~3 of the ~276** Cryptol-prelude defs in `cryptol-saw-core/saw/Cryptol.sawcore` (`Num`, `TCNum`, `TCInf`). Specialization usually unfolds Cryptol-prelude defs away; any residual class dictionary (`PCmp`, `PEq`, `PRing`, `PLogic`, `PIntegral`, …) fails as unknown-identifier.
- `exercises/sha512/` will fail today: `messageSchedule_Common` and `SHA_2_Common'` use `fix` over `[inf]` (Arc 4.4 territory). The recursion-free pieces (`Ch`, `Maj`, `processBlock_Common`, `Salsa20.quarterround`, `Point.point_add`) would translate cleanly.
- Smoketest covers the AST/pretty-printer but **does not exercise any `TranslationError` constructor**: only the success path. The other negative paths (`NotSupported`, `BadTerm`, `UnderAppliedMacro`, …) have zero pinned tests.
- Round-trip elaboration runs in-tree (`test-lean.sh` + the `lean-elaborate` flag file), but **CI invokes none of the integration tests** — `.github/workflows/ci.yml` references `saw-core-lean` zero times.

## Test coverage findings

### Rocq parity tests

The status doc table is stale. Current state (read from `.saw` drivers):

| Rocq test | Lean equivalent | Notes |
|---|---|---|
| `test_arithmetic` | `test_arithmetic.saw` | Mirrored (`t1`, `t3`–`t12`). |
| `test_boolean` | `test_boolean.saw` | Mirrored, plus partial-`ite` probes via `parse_core`. |
| `test_lambda` | `test_lambda.saw` | Mirrored (`t1`–`t5`). |
| `test_literals` | `test_literals.saw` | Mirrored modulo a documented octal corner-case. |
| `test_records` | `test_records.saw` | `t1`–`t7` only; **drops** Rocq's record-update battery (`t8`–`t15`) — those use `ecRecUpdate`-style primitives we haven't enumerated. **Real gap.** |
| `test_tuples` | `test_tuples.saw` | Mirrored (`t1`–`t7`). |
| `test_sequences` | `test_sequences.saw` | 16 of 23 cases. **Drops** `TestSeq_Comprehension` (`[x+1 | x <- xs]`) and `TestSeq_Transpose`; both lower onto Cryptol primitives (`ecFromTo`, `ecTranspose`) not in `SpecialTreatment.hs`. **Real gap.** |
| `test_typelevel` | `test_typelevel.saw` | Mirrored verbatim. The `bit0_macro` cosmetic problem is the open issue. |
| `test_offline_rocq` | `test_offline_lean.saw` | Mirrored (`t1`–`t4`). |
| `test_cryptol_module_simple` | `test_cryptol_module_simple.saw` | Same `Simple.cry` source. |
| `test_cryptol_module_sha512` | (deferred → `test_cryptol_module_sha_sigma.saw`) | Full SHA-512 functor parked behind Arc 4.4; the Lean side runs the recursion-free *sigma* slice instead. |
| `test_cryptol_primitives` | **missing** | No `write_lean_cryptol_primitives_for_sawcore` SAW command exists at all. Specialization makes a "dump every Cryptol-prelude axiom" form less natural; worth a one-line decision note rather than silent absence. |
| `test_prelude` | **missing** | Same shape — Lean side doesn't materialize the SAW prelude as a translatable module. Worth an explicit `NOT-APPLICABLE` note. |

The `intTests/test_lean_basic/` directory mentioned in the status doc **does not exist**; its four basic tests (`idBit`, `eqBit`, `literalNat`, `implRev4`) live as `test_idBool.saw` / `test_eqBool.saw` / `test_literalNat.saw` / `test_implRev4.saw` inside `otherTests/saw-core-lean/`. Pinned `.lean.good` files for each are present.

### Smoketest / unit-level gaps

`saw-core-lean/smoketest/SmokeTest.hs` (15 cases): 12 pretty-printer, 4 translator (lambda, polymorphic id, Bool constant, vector literal incl. empty), 1 goal-emission. Missing:

1. **No `TranslationError` triggers.** `Monad.hs` defines 7 constructors (`NotSupported`, `NotExpr`, `NotType`, `LocalVarOutOfBounds`, `BadTerm`, `CannotCreateDefaultValue`, `UnderAppliedMacro`, `UnsoundRecursor`). Only `UnsoundRecursor` is exercised, end-to-end via `intTests/test_lean_soundness_natrec`. The other six have **no test at all**.
2. **No `polymorphismResidual` positive battery.** The negative case is in `intTests/test_lean_soundness_polymorphic`; positive cases (`(a : Type) -> a -> a`, polymorphic over `Nat`, polymorphic over `Num`) are unpinned. A regression that started rejecting `Type` would silently break every Cryptol-module emission.
3. **No nested-let / large-Pi / weird-identifier pretty-printer cases.** Each existing case is single-construct. The `escapeIdent` Z-encoding path (`SpecialTreatment.hs:479`) is currently dead from a test perspective.
4. **No `findSpecialTreatment` lookup test.** With ~70 entries in the prelude treatment map, a typo could silently route the wrong identifier and the wrong output might still elaborate (e.g. `intLe` vs `intLt`).

### Negative / regression tests

Three intTests pin failure modes; all three still test what they claim:

- `test_lean_soundness_natrec` — synthetic `Nat#rec` term forces `UnsoundRecursor`. Stable.
- `test_lean_soundness_polymorphic` — `\\(t : sort 1) -> \\(x : t) -> x` triggers `polymorphismResidual` from `SAWCentral.Prover.Exporter`. Stable.
- `test_lean_soundness_error_prop` — pure-Lean test that the `error : Sort (u+1)` axiom shape rejects `error False ""` (would prove `False`) but accepts realistic uses. The most subtle of the three; the `attack.lean`/`non_prop.lean` probes are exactly the right scope.

No expected-fail tests exist for the other 5 `TranslationError` constructors.

## Cryptol surface findings

Cross-referencing `exercises/**/*.cry` against `SpecialTreatment.hs` and `SAWCorePrimitives.lean`:

### Exercises that would translate today (in pieces)
- **`exercises/functional-correctness/point/Point.cry`** — `point_add` is record + bv-`+`; uses `RecordType`/`RecordValue`/`Pair_fst`/`Pair_snd`/`bvAdd`/`bvEq`. All present. Property `point_add_commutes` would emit as an `offline_lean` goal.
- **`exercises/functional-correctness/swap/Swap.cry::swap_list`** — `update`, `@`, vector literals; primitives in scope. (`argmin`, `selection_sort` would not — see below.)
- **`exercises/functional-correctness/popcount/Popcount.cry::popCount`** — uses an `if elt then prev + 1 else prev` plus a self-referential comprehension `ic = [0] # [...| ... <- ic]`. The comprehension lowers to Cryptol-prelude defs not in the table; might or might not survive specialization at concrete `[32]`. Same shape as `rev.cry::Rev`. Uncertain without running.
- **`Salsa20.quarterround`, `littleendian`, `littleendian_inverse`** — pure bv ops over fixed-size arrays plus rotates and `reverse`/`split`/`join`. `rotateL`/`rotateR` are present (Arc 4.2). The split/join/reverse trio specializes to `gen`/`atWithDefault` — already exercised by `rev.cry::Rev`.

### Exercises that would partially translate
- **`Salsa20.Salsa20`, `Salsa20_expansion`, `Salsa20_encrypt`** — uses `zs = [xw] # [doubleround zi | zi <- zs]`, the SHA Merkle-Damgard shape. Needs Arc 4.4. Worth a `test_cryptol_module_salsa20_quarterround.cry` slice analogous to the existing `SHASigma.cry`.
- **`Swap.argmin`, `Swap.selection_sort`** — type-level recursion (Cryptol `go` recurses on a type-level index). At a concrete `n` may fully unfold; symbolic `n` likely hits `UnsoundRecursor`. Unverified.
- **`exercises/sha512/SHA.cry`** — `Ch`, `Maj`, `processBlock_Common` are the easy half (covered by the existing `test_cryptol_module_sha_sigma.saw`). `messageSchedule_Common`, `compress_Common`, `SHA_2_Common'`, `SHAUpdate` all use `fix`-style stream recursion.

### Exercises that would fail outright
- **`exercises/sha512/SHA512.cry` functor instantiation** — `module SHA512 = SHA where {...}` pulls in stream recursion.
- **`exercises/functional-correctness/u128/`** — only `.c`/`.saw` files, no `.cry`. Not a translator target.

### Primitives in Cryptol.sawcore / Prelude.sawcore not yet exercised

**`Prelude.sawcore` primitives** (108 total): ~70 are in `SpecialTreatment.hs::sawCorePreludeSpecialTreatmentMap`. Missing primitives that would surface as unknown-identifier errors if a user term reaches them post-`scNormalize`, grouped:

- *SMT-array*: `Array`, `arrayConstant`, `arrayLookup`, `arraySet`, `arrayCopy`, `arrayEq`, `arrayUpdate`, `arrayRangeEq`. Surface only via LLVM/MIR extracts. Defer.
- *Float*: `Double`, `Float`, `mkDouble`, `mkFloat`. Cryptol does have `Float`-typed code (`PFloat` class).
- *Rational*: `Rational`, `rational{Add,Sub,Mul,Neg,Recip,Eq,Le,Lt,Floor}`, `ratio`. Unused so far.
- *IntMod*: `IntMod`, `intMod{Add,Sub,Mul,Neg,Eq}`, `toIntMod`, `fromIntMod`. ECC code paths use these.
- *Other*: `bvForall`, `bvEqToEq`, `bvEqToEqNat`, `bvultToIsLtNat`, `equalNatToEqNat`, `expByNat`, `genWithProof`, `atWithProof`, `updWithProof`, `sliceWithProof`, `updSliceWithProof`, `proveLeNat`, `natCompareLe`, `intAbs`, `intMin`, `intMax`, `head`, `tail`, `zip`, `scanl`, `appendString`, `equalString`, `bytesToString`, `EmptyVec`, `fix` (deliberately rejected). `head`/`tail`/`zip`/`scanl` will surface in any non-trivial Cryptol code.

**`Cryptol.sawcore` defs** (276 total): only **3** are in the table — `Num`, `TCNum`, `TCInf`. Specialization unfolds most `ec*`-prefixed Cryptol-prelude defs into Prelude `bv*`/`gen`/etc primitives, which is why `rev.cry` and the sigma slice work without enumeration. Class dictionaries (`PCmp`, `PEq`, `PRing`, `PLogic`, `PLiteral`, `PIntegral`, `PField`, `PRound`, `PSignedCmp`, `PZero`, plus their per-type instances `PRingWord`, `PCmpVec`, …) are not in the table; whether they survive `scNormalize` depends on the surrounding term. The status doc's proposed `--dump-residual-primitives` flag (Arc 3) is the cheapest way to grow this systematically.

## Recommendations

In priority order, smallest wins first:

1. **`TranslationError` battery in `SmokeTest.hs`** (~30 minutes). One synthetic Term per constructor: a malformed term for `BadTerm`, an out-of-range DB index for `LocalVarOutOfBounds`, etc. `UnsoundRecursor` already has an intTest analog; moving a trigger into the smoketest avoids needing a saw binary on the path.
2. **`polymorphismResidual` positive battery** (~30 minutes). Three smoketests confirming `Type → α → α` (over `mkSort 0`), `Nat → ...`, and `Num → ...` are NOT rejected. Pairs naturally with the existing negative case. Likely best placed alongside `polymorphismResidual` in `SAWCentral`.
3. **`escapeIdent` smoketest** (~10 minutes). The Z-encoding path is dead from a test perspective; one identifier with a non-`[A-Za-z0-9_']` character exercises it.
4. **README notes for `test_cryptol_primitives` and `test_prelude`** (~10 minutes). One-line decision note per missing test. Avoids the recurring "where's our equivalent?" question.
5. **Slice tests for popcount and salsa20-quarterround** (~1 hour). Drop in `test_cryptol_module_popcount.saw` and `test_cryptol_module_salsa20_q.saw` as monomorphic single-Cryptol-file translations. Either they pass (confirming the exercises clean-elaborate) or they surface real primitive gaps. **Highest-value test addition** — converts "we think exercises/ would partially work" into pinned ground truth.
6. **Auto-derive `leanOpaqueBuiltins`** (~half day, status doc Arc 3). Right now every new opaque entry is a manual chore *and* soundness-critical — wrong opacity exposes `Nat#rec` and triggers `UnsoundRecursor`. A walk over the Prelude module map looking for `Nat#rec`/`Pos#rec` references in transitive bodies is mechanical.
7. **Wire CI** (~1 hour). Add `cabal test saw-core-lean-tests saw-core-lean-smoketest` to `.github/workflows/ci.yml`. `lean-elaborate.sh` already returns 77 (skip) when `lake` is missing.

**What NOT to spend time on yet**: native `BitVec` binding (Arc 3) is multi-week and can't be evaluated without first knowing whether real Cryptol codebases benefit. Until popcount/salsa20-quarterround/point/swap actually translate end-to-end (recommendation 5), there's no data for the BitVec call.

**Concrete answer to the framing question — *how much of Cryptol do we actually handle?*** Roughly any monomorphic, recursion-free Cryptol program whose primitives are in the ~95-element treatment map. That's enough for `point_add`, `quarterround`, `Ch`/`Maj`, and the SHA sigmas. Stops at any `[inf]`-stream `fix`, any class dictionary that survives normalization, any unstabilized Cryptol-prelude `ec*` form (record updates, list comprehensions in some shapes, `transpose`, …), and floats / rationals / mod-int types altogether.
