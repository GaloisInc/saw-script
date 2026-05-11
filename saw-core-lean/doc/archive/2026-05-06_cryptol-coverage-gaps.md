# Cryptol surface coverage — what fails and why
*2026-05-06* — *follow-ups landed 2026-05-07*

Companion to `2026-05-06_pre-merge-audit.md`. The pre-merge audit
covers the translator's internals (soundness, perf, docs); this note
focuses on the **input side**: which SAW workflows fail because the
Lean backend doesn't cover particular Cryptol/SAWCore constructs, and
how much effort each gap would take to close.

> **2026-05-07 status update.** The pre-merge effort summary's items
> 1, 2, 3, and 4 (CG-1 through CG-5 plus H-2) all landed. The
> *failure modes* described below remain accurate as a taxonomy, but
> the specific entries marked **CLOSED** have been resolved; see
> inline annotations and the diff against this commit hash. The
> "Pre-merge effort summary" table at the bottom of this document
> now reads as historical: the four-day plan ran in two passes
> (CG-1 / algebraic-enum / CG-4 / CG-5 / H-2). Item 5 (SMT arrays)
> remains deferred; CG-2 (class dictionaries) and CG-6
> (AES/SHA/EC primitives) remain on the long-term plan.

## The trust model

The Lean backend uses **specialization**: SAW's `scNormalize` unfolds
Cryptol surface primitives down to a small mapped set of Prelude
primitives before the translator runs. Concretely:

- **3** Cryptol-prefixed mappings: `Num`, `TCNum`, `TCInf` (the
  type-level naturals).
  See `src/SAWCoreLean/SpecialTreatment.hs:241-246`.
- **~150** Prelude-prefixed mappings (bitvector ops, `Either`, `Stream`,
  `Pair`, IntMod, Rational, Float, Double, …).
  See `src/SAWCoreLean/SpecialTreatment.hs:252-501`.
- Everything else in `cryptol-saw-core/saw/Cryptol.sawcore` (305
  identifiers — `ec*`, `P*Class`, `tc*`, `seq*`, `AES*`,
  `processSHA2_*`, `ec_double`, …) is **expected to vanish under
  normalization**.

When that assumption holds, translated output is clean. When it
doesn't, the user hits one of four failure modes below.

The translator audits the *Prelude* surface at startup
(`auditPreludePrimitivesForLean` in
`saw-central/.../Exporter.hs:865-895`) but does **not** audit the
*Cryptol* surface. New unmapped Cryptol primitives will not be
flagged.

> **CG-1 closed (2026-05-07).** Both the Prelude and Cryptol surfaces
> now reject by default: `defaultTreatmentFor` returns `UseReject`
> for any unmapped `ModuleIdentifier`, and the new
> `auditCryptolPrimitivesForLean` runs on every translator startup.
> The "fall-through to `UsePreserve`" in Failure mode B no longer
> happens.

## Failure mode A — clean reject at translation time (good UX)

Translator throws `RejectedPrimitive`, `UnsoundRecursor`, or
`polymorphismResidual` with helpful diagnostic text. Already audited
in the prior reports.

| Workflow that fails | Cryptol shape | Closing effort |
|---|---|---|
| Merkle-Damgård hashing (SHA family) | `Prelude.fix` over a stream-of-blocks accumulator that doesn't fit `StreamCorec` / `PairStreamCorec` / `BoundedVecFold` | LARGE — needs a fourth recognizer + soundness argument. Long-term plan §4 tracks this. |
| Factorial / iterative-over-counter | `fix` on `[8]` bitvector with `if` guard ("bitvector-gated partial recursion") | LARGE — would need a fuel/decision-procedure encoding |
| Algebraic `enum` types whose recursor escapes specialization | uses `Num#rec1` polymorphic dispatch | LARGE — universe-poly recursor mapping; correctly rejected by `polymorphismResidual` today |
| Functions polymorphic over `Type` | `f : {a : Type} -> ...` exported polymorphically | LARGE — same gate |

**These are correctly refused.** Effort here is to *expand* what's
accepted, not fix bugs. Out of scope for merge.

## Failure mode B — silent dangling reference, fails at `lake env lean` (bad UX) — **CLOSED 2026-05-07**

> **Historical**: this was the highest-impact UX gap for real users.
> `Term.hs:577` used to fall through to `UsePreserve` for any unmapped
> `ModuleIdentifier`, turning a SAW-side limitation into a downstream
> Lean compile error the user had to diagnose backwards.
>
> CG-1 promoted unmapped `ModuleIdentifier` to `UseReject` by default;
> the table below is preserved for the workflow taxonomy, but every
> "silent dangling reference" path is now a clean `RejectedPrimitive`
> at SAW translation time. Items still rejected (AES / SHA-2 / EC /
> SMT-array / class dictionaries) carry user-meaningful messages
> pointing at CG-2/3/6.

| Workflow that fails | Why it bites | Closing effort |
|---|---|---|
| **Polymorphic Cryptol export with class constraint** — e.g. `f : {a} (Ring a) => a -> a -> a` left polymorphic at the `write_lean_*` call site | `PRing` dictionary doesn't monomorphize; `ecPlus` survives as `Cryptol.ecPlus` | MEDIUM — map each `P*Class` dictionary's projections to Lean type-class methods, OR document that all entry points must be monomorphized first. Long-term plan §6 explicitly defers this. ~2-3 days for a Ring/Eq/Cmp/Logic pass. |
| **AES verification** (`examples/openssl_aes/AES128TBox.cry` and similar) | Uses `AESEncRound`, `AESEncFinalRound`, `AESInvMixColumns`, `AESKeyExpand` — all unmapped | LARGE — each needs a Lean realisation matching SAW's primitive declaration. ~1 week per primitive if axiomatized; longer for a real implementation |
| **SHA-2 verification** | Uses `processSHA2_224/256/384/512` primitives unmapped, plus the `Num#rec1` dispatch issue from failure mode A | LARGE — same shape as AES |
| **ECDSA verification** (`examples/ecdsa/cryptol-spec/`) | Uses `ec_double`, `ec_mult`, `ec_twin_mult`, `ec_add_nonzero`, `ProjectivePoint` — all unmapped | LARGE |
| **SMT-array LLVM extracts** | `Array`, `arrayLookup`, `arraySet`, `arrayCopy`, `arrayEq`, `arrayUpdate`, `arrayRangeEq`, `arrayConstant` are explicit `reject` entries today (post-CG-1; the old `leanIntentionallyUnmappedPrimitives` allow-list is gone). Affects any `llvm_verify` against extractions using the SMT-array memory model. | MEDIUM — implement a Lean realisation backed by `Std.HashMap` (or similar) with `arrayLookup`/`arraySet` semantics; ~3-5 days. CG-3 in current planning. |
| ~~**String operations**~~ — **CLOSED CG-4 2026-05-07** | mapped to Lean's `String.append` / `String.beq` / Vec-of-bytes fold via `Char.ofNat`; surfaces in every Cryptol `error "msg"` workflow | (closed) |
| **Vector with-proof variants** | `atWithProof`, `genWithProof`, `updWithProof`, `sliceWithProof`, `updSliceWithProof` unmapped | MEDIUM — Cryptol uses these for safe indexing; need Lean equivalents that carry the bound proof |
| **`ecRandom` / `ecParmap` / `ecTrace` / `ecDeepseq`** | meta/IO-flavored ops, unmapped | TRIVIAL — refuse cleanly with `RejectedPrimitive` ("not meaningful in a translated proof") |

**Top recommendation:** add an `auditCryptolPrimitivesForLean`
analogue of `auditPreludePrimitivesForLean`. Walk the Cryptol module
map at translator startup; any `Cryptol.*` ident that isn't either
(a) explicitly mapped or (b) in a new
`cryptolIntentionallyUnmappedPrimitives` exception list refuses at
translation time with a clean `RejectedPrimitive` diagnostic.

**~1 day of work**, eliminates an entire class of "Lean elaboration
failed mysteriously" support reports. The user gets "we can't
translate `AESEncRound`" instead of "Lean: unknown identifier
`CryptolToLean.Cryptol.AESEncRound`".

## Failure mode C — translates and elaborates, but doesn't compute (subtle)

The reference resolves to a Lean axiom; the elaborator is happy; the
user proof can't `decide` / `rfl` / `simp` past the opaque symbol. The
translator did its job, but the resulting Lean term has no
operational semantics for the construct.

| Construct | What survives | Effort to make computable |
|---|---|---|
| `Float` / `Double` / `mkFloat` / `mkDouble` | mapped to opaque Lean axioms (no IEEE-754 model) | LARGE — full IEEE-754 model in Lean. Or: keep opaque and document that float "verification" is structural-only |
| `Prelude.error` (when reached during elaboration of a user proof) | mapped to `error_unrestricted` axiom | by-design — `error` shouldn't compute. Document. |
| Various unmapped SAW-proof lemmas (`bvForall`, `bvEqToEq`, `bvEqToEqNat`, `bvultToIsLtNat`, `equalNatToEqNat`, `expByNat`, `proveLeNat`, `natCompareLe`, `intAbs`/`Min`/`Max`, `eqNatPrec`, `eqNatAdd0`/`AddS`/`AddComm`, `addNat_assoc`, `IsLtNat_*`, `IsLeNat_*`, `bvult_*`, `bveq_*`, etc.) | post-CG-1 these are explicit `reject` entries with user-facing messages; a SAW proof obligation that reaches one rejects at translation time rather than landing as an unknown identifier in Lean | MEDIUM each — write the Lean proof. The SAW Prelude has ~30 such lemmas; many are simple `decide`/`omega`/`rfl` discharges. Tracked under CG-2/CG-6 in the current plan. |

## Failure mode D — untested but probably works

These have a path through the translator but no driver/proof coverage
in the current test corpus. Most likely work; some have edge cases
that haven't been probed.

| Construct | Likely status | Closing effort |
|---|---|---|
| ~~Cryptol algebraic `enum` types~~ — **CLOSED CG-5 2026-05-07** | A clean reject lands at the SAW boundary via `discoverEnumEncodingReachers` keeping `ListSort`/`FunsTo` opaque so the user sees a "Cryptol algebraic enum case-analysis" diagnostic instead of an `scLambda` panic. Lean-side realisation of the encoding still TBD (would unblock `Maybe a` / `Either`-style enums end-to-end). | (rejection closed; full mapping deferred to long-term plan §6) |
| ~~Record updates (`r.{field = v}`)~~ — **CLOSED CG-5 2026-05-07** | Translates today via the existing `RecordType` encoding (no new translator code needed; pinned by `drivers/cryptol_module_record_update/`). | (closed) |
| Tuple proofs | drivers emit-diff tuples; `proofs/tuple_fst/` now pins one shape | (largely closed; further proofs cheap) |
| ~~Mutual streams beyond `streamFibs` driver-emit~~ — **CLOSED H-2 2026-05-07** | `proofs/stream_fibs_corec/` discharges three concrete fib values, including the cross-stream `lkα + lkβ` recursion path. | (closed) |
| `Integer` at top-level (vs nested in arithmetic) | no top-level driver; only inside `implRev4`-style indexing | TRIVIAL — driver. ~½ day |
| `parse_core` partial-application beyond t6-t9 | one driver covers a few shapes; broader shapes untested | SMALL |

## Pre-merge effort summary — **all four landed 2026-05-07**

The smallest useful set to give users **clean diagnostics on the full
Cryptol surface** (even where translation can't proceed) was:

| # | Item | Effort | Effect | Status |
|---|------|--------|--------|--------|
| 1 | Cryptol-side audit gate (refuse unmapped `Cryptol.*` cleanly) | ~1 day | Eliminates failure mode B *as a UX issue* | **CLOSED CG-1** (default-`UseReject` + `auditCryptolPrimitivesForLean`) |
| 2 | String primitives (`appendString`, `equalString`, `bytesToString`) | ~1 day | Common, small | **CLOSED CG-4** |
| 3 | Cryptol algebraic-`enum` reject + record-update driver | ~1 day | Closes untested D items | **CLOSED CG-5** (algebraic enum: clean reject; record-update: translates via `RecordType`) |
| 4 | Mutual-stream proof + tuple proof | ~1 day | Closes audit H-2 + tuple coverage gap | **CLOSED H-2** (`proofs/stream_fibs_corec/`) |

The four items shipped in two passes. No soundness change; everything
produced test artifacts that lock in the surface and make subsequent
expansion safer.

Optional larger item:

| # | Item | Effort | Effect |
|---|------|--------|--------|
| 5 | SMT-array primitives | ~3-5 days | Unlocks LLVM-with-array-memory verification (`crucible_array`-style extracts) |

Item 5 is a judgment call. Needed for serious LLVM verification
workflows, but not on the critical path if the merge target audience
is Cryptol-property verification rather than memory-model extracts.

## What cannot be made cheap

The following are **not** "engineering items": they're effectively
small research projects, and any merge claim should be explicit about
which workflows they exclude.

- **AES round / SHA-2 / EC primitives** as named SAWCore primitives —
  each needs a Lean realisation; the upstream Cryptol/SAW Prelude
  axiomatizes them, so a Lean-side axiomatization with the same shape
  is feasible (~1 week per primitive) but *uses* of those axioms in
  user proofs won't compute, which limits utility.
- **`Float` / `Double` semantics** — Lean has no built-in IEEE-754
  model; mathlib has partial coverage. Full bit-exact float verification
  is a multi-month project.
- **Polymorphic class-dictionary surface** — medium-to-large per class
  if you map to Lean type classes; medium overall if you instead just
  refuse polymorphic-at-export-site usage with a clear error.
- **`fix`-shape expansion for hash functions** — open research item
  (`long-term-plan.md` §4 / `recursion-design.md`). The current three
  shapes (`StreamCorec`, `PairStreamCorec`, `BoundedVecFold`) cover
  Cryptol's productive-corec idiom; SHA-shaped accumulators don't fit.

## Recommendation

Land items 1-4 as part of merge (~4 days). Defer item 5 unless an
LLVM-array workflow is in the immediate post-merge plan. Document the
cannot-be-made-cheap list explicitly in `README.md` "What's punted"
so users with AES/SHA/ECDSA verification workflows know up-front that
the Lean backend isn't the right tool for their case today, and
neither the user nor the maintainer wastes time on a triage cycle.

Item 1 (the Cryptol-side audit gate) is the single highest-leverage
change: it's small, soundness-neutral, and converts the most painful
class of user-visible failures from "mysterious Lean error" into "SAW
explained why it can't help and what the workaround is".
