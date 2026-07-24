# Differential Conformance Plan

**Status (added 2026-07-24)**: NORTH-STAR SCOPE document — the
target conformance surface, not a statement of current state.
Current coverage lives in `otherTests/saw-core-lean/CONFORMANCE.md`
(the per-surface matrix) and STATUS.md (the census). Note one
sharpening since this was written: `bvToInt` is UNSIGNED and
`sbvToInt` SIGNED — the split is load-bearing and differentially
pinned on sign-crossing inputs (2026-07-23).

## Goal

The conformance suite is a coverage suite for SAWCore. Its long-term acceptance
criterion is complete semantic parity with SAWCore for the Lean backend.

That means every SAWCore construct must be represented in the suite. A construct
is not excluded because the current backend rejects it, because the current Lean
library marks it `noncomputable`, or because the current observer is awkward.
Those are backend or library gaps, and the suite should catch them.

A positive executable conformance test is valid only when:

1. SAW observes a result using its real evaluator, checker, or proof-obligation
   machinery;
2. SAW-Lean emits the corresponding Lean artifact;
3. Lean observes the emitted artifact itself; and
4. the harness mechanically compares the observations.

Golden diffs, Lean elaboration, and standalone support-library proofs are useful
regression signals, but they are not semantic conformance by themselves. Large
examples are integration or stress tests. They may suggest litmus cases, but
they do not replace focused SAWCore coverage.

The suite should distinguish current status from final scope:

- `green`: the construct has a passing SAW-vs-Lean value or obligation test;
- `known-gap`: the construct is in SAWCore and must be supported, but the
  current backend or Lean library cannot pass it yet;
- `semantic-boundary`: the construct is partial or proof-carrying, so the
  correct final behavior is an explicit Lean proof obligation rather than an
  unchecked value;
- `integration-only`: large programs that are useful stress tests but do not
  define coverage.

Passing the complete conformance suite means there are no `known-gap` entries
left for supported SAWCore. Temporary expected-failure tests are allowed only as
gap markers; they are not evidence of parity.

## Ground Truth: Core SAWCore

The plan is grounded in the actual SAWCore AST.

`saw-core/src/SAWCore/Term/Functor.hs` defines the core term constructors:

- `App`
- `Lambda`
- `Pi`
- `Constant`
- `Variable`
- `FTermF (Recursor CompiledRecursor)`
- `FTermF (Sort Sort SortFlags)`
- `FTermF (ArrayValue e (Vector e))`
- `FTermF (StringLit Text)`

`CompiledRecursor` records:

- datatype name;
- elimination sort;
- number of parameters;
- number of indices;
- constructor order.

Constructor order is a soundness surface. SAW's `Bool` constructors are
`True; False`, while Lean's generated `Bool.rec` is false-first. Any direct
recursor mapping must be tested and justified, not assumed.

`SortFlags` records `flagInhabited` and `flagQuantType`. The flags are advisory
for Rocq export and do not affect SAWCore typechecking, but the Lean backend
still needs coverage for every emitted sort/universe shape it uses.

`saw-core/src/SAWCore/Module.hs` defines the module surface:

- ordinary definitions with bodies;
- primitive declarations;
- axiom declarations;
- datatype declarations;
- constructors and constructor argument structure;
- datatype parameters and indices;
- injected code declarations.

`saw-core/src/SAWCore/Parser/AST.hs` adds surface syntax that must be covered as
user-facing input, even when it elaborates to smaller core constructs:

- imports and module declarations;
- type declarations, term definitions, typed definitions, data declarations,
  primitive declarations, axiom declarations, injected code;
- names and qualified names;
- `Sort`, `App`, `Lambda`, `Let`, `Pi`, `Recursor`;
- records, tuples, projections, and updates;
- type constraints;
- natural, string, vector, and bitvector literals.

`saw-core/src/SAWCore/Simulator/Value.hs` describes the concrete value shapes SAW
can observe:

- functions;
- constructors and constructor muxes;
- vectors;
- Booleans;
- words/bitvectors;
- Nat, Int, IntMod, Rational;
- arrays;
- strings;
- extra simulator values such as streams;
- type values.

The coverage matrix must cross these core constructs with the prelude and
Cryptol primitive families below.

## SAWCore Prelude Surface To Cover

The authoritative source is `saw-core/prelude/Prelude.sawcore`.

### Core Control And Errors

Cover:

- `id`
- `fix`
- `sawLet`
- `error`

`fix` and recursive/totality reasoning are semantic-boundary cases until the
backend emits Lean proof obligations that justify the recursion. They still
belong in the conformance matrix.

### Datatypes And Recursors

Every datatype needs constructor coverage, recursor coverage, and at least one
small elimination test where the semantics are executable.

Prelude datatypes:

- `UnitType`
- `PairType`
- `PairType1`
- `Void`
- `Eq`
- `EqDep`
- `EmptyType`
- `RecordType`
- `Bool`
- `Either`
- `Maybe`
- `Pos`
- `Nat`
- `Z`
- `AccessiblePos`
- `AccessibleNat`
- `IsLeNat`
- `Stream`
- `List`
- `ListSort`
- `FunsTo`

Current direct-recursion hazards such as `Bool#rec`, `Nat#rec`, `Pos#rec`,
`Z#rec`, `AccessiblePos#rec`, and `AccessibleNat#rec` must be represented as
known gaps or proof-obligation tests, not omitted. User-defined datatypes are
also part of SAWCore parity and need a tiny coverage path.

### Equality, Coercion, And Proof Terms

Cover value behavior where possible and proof-obligation shape otherwise:

- `Eq`, `Refl`, `Eq__rec`, `EqDep`;
- `uip`;
- `eq_cong`, `sym`, `trans`, `trans2`, `trans4`, `eq_inv_map`;
- `fix_unfold`;
- `unsafeAssert`;
- `coerce`, `coerce__def`, `coerce__eq`, `coerce_same`, `coerce_trans`,
  `rcoerce`, `unsafeCoerce`, `piCong0`, `piCong1`;
- proof lemmas for pairs, records, Booleans, Nat, vectors, and bitvectors.

No equality/proof primitive may become a trusted Lean axiom merely because SAW
has an axiom. The final backend must either emit a Lean-checkable proof
obligation/certificate or clearly mark the construct as outside the supported
sound fragment. The conformance suite should expose that decision.

### Products, Records, Unit, Empty, Either, Maybe

Cover:

- pair construction, projection, equality, `fst`, `snd`, `uncurry`;
- type-level pair operations from `PairType1`;
- empty records and record tails;
- `RecordType`, `RecordValue`, `headRecord`, `tailRecord`, update-like uses;
- `Either`, `Left`, `Right`, `either`, `boolToEither`;
- `Maybe`, `Just`, `Nothing`, `maybe`;
- `UnitType`, `Void`, `EmptyType`, and their eliminators.

### Bool

Cover:

- constructors `True` and `False`;
- `iteDep`, `ite`, and their branch-order lemmas;
- `iteWithProof` and `ifWithProof`;
- `not`, `and`, `or`, `xor`, `boolEq`, `implies`;
- Boolean equality and ordering through Cryptol dictionaries;
- Boolean proof lemmas as proof-obligation or proof-checking cases.

Direct `Bool#rec` is not optional coverage. It is a required soundness test.
The current correct behavior may be a rejection/gap, but the construct must stay
visible until there is a proof-carrying or otherwise justified implementation.

### Nat, Pos, Z, And Order Proofs

Cover:

- `Pos`, `Nat`, and `Z` constructors and cases;
- numeric literals and macro/elaboration paths;
- `posInc`, `posAdd`, `posMul`, `posExp`, `posEq`, `posLe`, `posLt`;
- `Succ`, `addNat`, `subNat`, `mulNat`, `expNat`, `equalNat`, `ltNat`,
  `leNat`, `minNat`, `maxNat`, `widthNat`, `pred`;
- `divModNat`, `divNat`, `modNat`, including zero-divisor behavior;
- `Nat__rec`, `Nat_cases`, `Nat_cases2`, `natCase`, `if0Nat`;
- `IsLeNat`, `IsLtNat`, `natCompareLe`, `proveEqNat`, `proveLeNat`,
  `proveLtNat`, and proof conversion lemmas;
- `expByNat`.

If a current SAW observation path panics on a closed term such as `leNat`, that
is a conformance-harness gap to track, not a reason to remove `leNat` from the
matrix.

### Vectors And Finite Sequences

Cover the primitive vector surface:

- `Vec`
- `gen`
- `head`
- `tail`
- `atWithDefault`
- `EmptyVec`
- `zip`
- `foldr`
- `foldl`
- `scanl`
- `rotateL`
- `rotateR`
- `shiftL`
- `shiftR`

Cover derived vector definitions:

- `at`
- `ConsVec`
- `upd`
- `map`
- `zipWith`
- `replicate`
- `single`
- `reverse`
- `transpose`
- `vecEq`
- `take`
- `drop`
- `slice`
- `join`
- `split`
- `append`
- little-endian join/split
- `pmux`

Also cover vector proof lemmas (`head_gen`, `tail_gen`, `foldr_nil`,
`foldr_cons`, `foldl_nil`, `foldl_cons`, `vecEq_refl`, `take0`, `drop0`) as
proof-obligation/proof-checking cases.

`ArrayValue` coverage belongs here: finite vector and bitvector literals should
force the literal core atom, independent of the SMT-array primitive family.

### Strings

Cover:

- `String`;
- `StringLit`;
- `appendString`;
- `bytesToString`;
- `equalString`;
- string-producing error paths.

### Bitvectors

Cover all primitive bitvector operations:

- `bvNat`, `bvToNat`;
- `bvAdd`, `bvNeg`, `bvSub`, `bvMul`, `bvLg2`;
- unsigned comparisons `bvugt`, `bvuge`, `bvult`, `bvule`;
- signed comparisons `bvsgt`, `bvsge`, `bvslt`, `bvsle`;
- `bvPopcount`, `bvCountLeadingZeros`, `bvCountTrailingZeros`;
- `bvForall`;
- `bvUDiv`, `bvURem`, `bvSDiv`, `bvSRem`;
- shifts `bvShl`, `bvShr`, `bvSShr`;
- integer conversions `intToBv`, `bvToInt`, `sbvToInt`.

Cover derived bitvector operations:

- `msb`, `lsb`, `bvAt`, `bvUpd`;
- `bvRotateL`, `bvRotateR`, `bvShiftL`, `bvShiftR`, `bvSShiftR`;
- `bvCarry`, `bvSCarry`, `bvAddWithCarry`, `bvSBorrow`;
- `bvZipWith`, `bvNot`, `bvAnd`, `bvOr`, `bvXor`, `bvEq`, `bvNe`,
  `bvNonzero`;
- `bvBool`, `bvTrunc`, `bvUExt`, `bvSExt`, `bvMin`;
- polynomial multiplication and modulus.

Cover BV proof primitives and lemmas as proof obligations:

- `bvNat_bvToNat`;
- `bvAddZeroL`, `bvAddZeroR`;
- `bvEq_refl`, `equalNat_bv`;
- `unsafeAssertBVULt`, `unsafeAssertBVULe`;
- `bvEqToEq`, `bvEqToEqNat`, `bvultToIsLtNat`;
- `not_bvult_zero`, `trans_bvult_bvule`, `bvult_sub_add_bvult`,
  `bvult_sum_bvult_sub`, `IsLtNat_to_bvult`, `bvult_to_IsLtNat`;
- `BV_complete_induction`;
- SHA-related BV lemmas at the end of the prelude.

Lean-side `noncomputable` markings do not remove these from conformance. They
may force a `#reduce` observer, a proof-obligation observer, or a known-gap
marker.

### Streams

Cover:

- `Stream`, `MkStream`, `Stream__rec`;
- `streamUpd`, `bvStreamUpd`;
- `streamGet`;
- `streamConst`, `streamMap`, `streamMap2`;
- `streamTake`, `streamDrop`, `streamAppend`;
- `streamJoin`, `streamSplit`;
- `streamShiftL`, `streamShiftR`;
- `streamScanl`.

Stream cases are important because they cross recursors, functions, infinite
values, and finite observations. The litmus tests should observe finite
projections.

### Integers, Modular Integers, Floats, Arrays, Rationals

Cover integer primitives:

- `Integer`;
- `intAdd`, `intSub`, `intMul`, `intDiv`, `intMod`;
- `intMin`, `intMax`, `intNeg`, `intAbs`;
- `intEq`, `intLe`, `intLt`;
- `intToNat`, `natToInt`;
- `intEven`.

Cover modular integer primitives:

- `IntMod`;
- `toIntMod`, `fromIntMod`;
- `intModEq`, `intModAdd`, `intModSub`, `intModMul`, `intModNeg`.

Cover floating primitives:

- `Float`, `mkFloat`;
- `Double`, `mkDouble`;
- Cryptol floating wrappers listed below.

The current lack of a clean Lean observation for float values is a known gap,
not a scope exclusion.

Cover SMT-array primitives:

- `Array`;
- `arrayConstant`;
- `arrayLookup`;
- `arrayUpdate`;
- `arrayCopy`;
- `arraySet`;
- `arrayRangeEq`;
- `arrayEq`.

Arrays are in SAWCore and need conformance coverage. Current rejection tests
are only temporary gap markers unless we explicitly decide arrays are outside
the backend's supported SAWCore fragment.

Cover rational primitives and derived operations:

- `Rational`;
- `ratio`;
- `rationalEq`, `rationalLe`, `rationalLt`;
- `rationalAdd`, `rationalSub`, `rationalMul`, `rationalNeg`;
- `rationalRecip`, `rationalDiv`;
- `rationalFloor`, `rationalCeiling`, `rationalTrunc`,
  `rationalRoundAway`, `rationalRoundToEven`;
- `integerToRational`, `rationalZero`, `rationalHalf`.

Zero denominators and reciprocal/division by zero are semantic-boundary tests:
the final backend should emit Lean obligations or checked preconditions, not
silently totalize them.

## Cryptol SAWCore Surface To Cover

The authoritative source is `cryptol-saw-core/saw/Cryptol.sawcore`.

### Num And Type-Level Arithmetic

Cover:

- datatype `Num` with `TCNum` and `TCInf`;
- `Num_rec`, `tcFin`, `getFinNat`, `finNumRec`, `finNumRec2`;
- `binaryNumFun`, `ternaryNumFun`, `binaryNumPred`;
- `tcWidth`, `tcAdd`, `tcSub`, `tcMul`, `tcDiv`, `tcMod`, `tcExp`,
  `tcMin`, `tcMax`;
- `ceilDivNat`, `ceilModNat`, `tcCeilDiv`, `tcCeilMod`;
- `tcLenFromThenTo_Nat`, `tcLenFromThenTo`;
- `tcEqual`, `tcLt`.

Include finite and infinite cases. Division/modulus preconditions must become
obligations where Cryptol semantics require them.

### Sequences, Streams, And Comprehensions

Cover:

- `seq`, `seq_TCNum`, `seq_TCInf`;
- `seqMap`, `seqConst`, `seqInhabited`;
- `IntModNum`;
- `eListSel`;
- comprehensions `from` and `mlet`;
- `seqZip`, `zipSame`, `seqZipSame`;
- `seqBinary`;
- `ecTake`, `ecDrop`, `ecCat`, `ecJoin`, `ecSplit`, `ecReverse`,
  `ecTranspose`;
- `ecAt`, `ecAtBack`, `ecUpdate`, `ecUpdateEnd`;
- finite and infinite range producers:
  `ecFromTo`, `ecFromToLessThan`, `ecFromThenTo`, `ecFromToBy`,
  `ecFromToByLessThan`, `ecFromToDownBy`, `ecFromToDownByGreaterThan`,
  `ecInfFrom`, `ecInfFromThen`;
- `ecFoldl`, `ecFoldlPrime`, `ecScanl`;
- `ecParmap`, `ecDeepseq`, `ecTrace`, `ecRandom`.

Infinite sequence tests should observe finite projections.

### Type Coercions And Congruences

Cover:

- `seq_cong`, `seq_cong1`, `IntModNum_cong`;
- `fun_cong`;
- `pair_cong`, `pair_cong1`, `pair_cong2`;
- `record_cong`, `record_cong1`, `record_cong2`;
- `unsafeAssert_same_Num`.

These are proof-carrying surfaces, not Haskell rewrite opportunities.

### Dictionaries And Overloaded Operations

Cover dictionary construction and use for:

- equality: `PEq*`;
- comparison: `PCmp*`;
- signed comparison: `PSignedCmp*`;
- zero: `PZero*`;
- logic: `PLogic*`;
- ring: `PRing*`;
- integral: `PIntegral*`;
- field: `PField*`;
- rounding: `PRound*`;
- literals: `PLiteral*`, `PLiteralLessThan`, `PFLiteral*`.

Cover overloaded entry points:

- `ecNumber`, `ecFromZ`, `ecFromInteger`;
- `ecPlus`, `ecMinus`, `ecMul`, `ecNeg`;
- `ecToInteger`, `ecDiv`, `ecMod`, `ecExp`;
- `ecRecip`, `ecFieldDiv`;
- `ecCeiling`, `ecFloor`, `ecTruncate`, `ecRoundAway`, `ecRoundToEven`;
- `ecEq`, `ecNotEq`, `ecLt`, `ecGt`, `ecLtEq`, `ecGtEq`, `ecSLt`;
- `ecAnd`, `ecOr`, `ecXor`, `ecCompl`, `ecZero`;
- `ecFraction`.

The suite should test representative dictionaries for Bool, Integer, Rational,
IntMod, finite bitvectors, finite vectors, pairs, records, unit, empty records,
functions, and streams where the source defines them.

### Cryptol Bitvector And Sequence Operators

Cover:

- `bvExp`;
- `ecLg2`, `ecSDiv`, `ecSMod`, `toSignedInteger`;
- `ecShiftL`, `ecShiftR`, `ecSShiftR`;
- `ecRotL`, `ecRotR`;
- `ecTrunc`, `ecUExt`, `ecSExt`;
- `ecSgt`, `ecSge`, `ecSlt`, `ecSle`;
- polynomial operations `ecPmult`, `ecPmod`.

### Cryptol Records, Tuples, Functions, Errors, And Comparisons

Cover:

- `const`, `compose`;
- `updFst`, `updSnd`, `updHeadRecord`, `updTailRecord`;
- `unitUnary`, `unitBinary`, `pairUnary`, `pairBinary`, `emptyUnary`,
  `emptyBinary`, `recordUnary`, `recordBinary`, `funBinary`;
- `errorUnary`, `errorBinary`, `ecError`;
- `boolCmp`, `boolLt`, `integerCmp`, `rationalCmp`, `bvCmp`, `bvSCmp`,
  `vecCmp`, `vecLt`, `unitCmp`, `unitLe`, `unitLt`, `pairCmp`, `pairLt`,
  `emptyCmp`, `emptyLe`, `emptyLt`, `recordEq`, `recordCmp`, `recordLt`.

### Cryptol Arrays, Floats, And Cryptographic Primitives

Cover array wrappers:

- `ecArrayConstant`, `ecArrayLookup`, `ecArrayUpdate`, `ecArrayCopy`,
  `ecArrayEq`, `ecArraySet`, `ecArrayRangeEq`.

Cover floating wrappers:

- `TCFloat`;
- `PEqFloat`, `PCmpFloat`, `PZeroFloat`, `PRingFloat`, `PFieldFloat`,
  `PRoundFloat`, `PLiteralFloat`, `PFLiteralFloat`;
- `ecFpNaN`, `ecFpPosInf`, `ecFpFromBits`, `ecFpToBits`, `ecFpEq`,
  `ecFpAdd`, `ecFpSub`, `ecFpMul`, `ecFpDiv`, `ecFpToRational`,
  `ecFpFromRational`;
- `fpIsNaN`, `fpIsInf`, `fpIsZero`, `fpIsNeg`, `fpIsNormal`,
  `fpIsSubnormal`, `fpFMA`, `fpAbs`, `fpSqrt`.

Cover cryptographic primitive declarations as either real differential tests or
explicit known gaps:

- AES round/key-expansion primitives;
- SHA2 processing primitives;
- elliptic-curve/projective-point helpers.

These are not good first litmus tests, but they are still part of the complete
SAWCore/Cryptol-SAWCore surface. They should be represented in the matrix, with
small focused tests wherever possible.

## Observability Policy

SAWCore is executable. If the current Lean model marks an otherwise executable
definition `noncomputable`, that is a Lean-model issue, not a conformance-scope
issue.

For each construct, choose the strongest honest observer available:

1. `#eval` of the emitted artifact when available;
2. `#reduce` of a closed emitted artifact when kernel reduction is available;
3. a Lean theorem/proof-obligation check when the construct is proof-carrying;
4. a known-gap test when no honest Lean observation exists yet.

Do not synthesize a hand-written Lean analogue in the observer. Do not use
`native_decide`, unchecked axioms, or Haskell-side rewrites as evidence of
semantic agreement.

## Suite Structure

The suite should be organized by SAWCore coverage, not by legacy examples.

The current harness-level buckets are:

- `differential/*`: positive executable litmus tests. SAW observes an outcome,
  Lean observes the SAW-Lean emitted artifact, and the harness mechanically
  compares those observations.
- `differential/*/.known-gap`: the real differential run fails at a pinned SAW
  producer, emitted-Lean, or Lean observer diagnostic listed in
  `.known-gap.expected`. This records missing parity or an observation-path
  blocker; it is not a passing conformance case.
- `saw-boundary/*`: expected rejection or proof-obligation boundary tests.
- `saw-boundary/*/.known-gap`: expected rejection tests that pin current
  backend/library gaps rather than final boundaries.

The coverage matrix maps those harness directories back onto the conceptual
buckets: core syntax, module syntax, Prelude families, Cryptol.sawcore families,
proof-obligation surfaces, and known gaps.
`make test-saw-core-lean-conformance` from the `deps/saw-script` repository
root should enumerate all of these focused litmus tests and report remaining
known gaps visibly. The local `otherTests/saw-core-lean` equivalent is
`make conformance`. The roadmap should optimize toward moving every known gap
into a green value or proof-obligation test.

## Implementation Plan

1. Build a machine-readable coverage matrix from `Prelude.sawcore`,
   `Cryptol.sawcore`, and the core AST constructors listed above.
2. Keep each test tiny: one constructor, primitive, recursor, or obligation
   shape per litmus whenever possible.
3. For each matrix row, record:
   - SAWCore source construct;
   - expected semantic category: value, type-level, proof obligation, partial
     precondition, or module/injection behavior;
   - SAW observation method;
   - Lean emitted artifact;
   - Lean observation method;
   - current status: green or known-gap.
4. Migrate existing useful legacy drivers by extracting only the smallest
   litmus cases that map to matrix rows.
5. Add gap tests immediately for unsupported current surfaces: dangerous
   recursors, arrays, floats, proof primitives, vector with-proof variants,
   noncomputable-but-executable Lean definitions, and any SAW evaluator/harness
   panic.
6. As backend work proceeds, convert known-gap tests to green tests without
   removing the coverage row.

## Acceptance Criteria

The differential conformance effort is complete only when:

- every core SAWCore term constructor has coverage;
- every parser/module construct that can reach the backend has coverage;
- every Prelude datatype, primitive, axiom/proof surface, and derived function
  family above has coverage;
- every Cryptol.sawcore datatype, dictionary family, overloaded entry point,
  sequence operator, array/float/crypto wrapper, and proof surface above has
  coverage;
- every partial operation emits a checked Lean precondition/obligation or has a
  documented final out-of-scope decision;
- no semantic behavior depends on clever Haskell equivalence code;
- all current `noncomputable` Lean-library limitations are either fixed or
  represented by tests that still observe the emitted artifact honestly.
