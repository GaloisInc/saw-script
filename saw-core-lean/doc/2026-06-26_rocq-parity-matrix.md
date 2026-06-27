# Rocq Parity Matrix

*2026-06-26. Working tracker for making `saw-core-lean` mirror the
user-visible `saw-core-rocq` backend, while leaving room for Lean-specific
extensions beyond Rocq.*

## Goal

The baseline goal is Rocq feature parity:

- every Rocq command has a Lean analogue, or a documented reason why the
  checked-in Lean support library replaces that command;
- every Rocq regression driver has a Lean driver, a Lean boundary rejection, or
  a documented soundness/design gap;
- generated Lean must elaborate, or SAW must reject before writing a misleading
  file;
- no parity item is allowed to pass by erasing `Except.error`, widening axioms,
  or relying on unchecked Haskell-side reasoning.

Lean can exceed Rocq later. The immediate extension target is using Lean as a
proof backend for obligations that are commonly sent to SMT. That work sits on
top of the parity baseline; it must not blur whether Rocq parity itself is done.

## Public API Surface

| Rocq command | Lean status | Notes |
| --- | --- | --- |
| `write_rocq_term` | Mirrored by `write_lean_term` | In active tests across arithmetic, boolean, lambda, literals, records, sequences, tuples, and typelevel drivers. |
| `write_rocq_cryptol_module` | Mirrored by `write_lean_cryptol_module` | In scope. Current Lean suite has many module drivers, but full SHA512 parity is not complete. |
| `write_rocq_sawcore_prelude` | Mirrored by `write_lean_sawcore_prelude` | Focused driver elaborates the emitted prelude. |
| `write_rocq_cryptol_primitives_for_sawcore` | Mirrored by `write_lean_cryptol_primitives_for_sawcore` | Focused driver emits the Cryptol primitives module and elaborates the generated Lean. |
| `offline_rocq` | Mirrored by `offline_lean` | Basic Rocq properties are mostly mirrored; Lean also has LLVM/Cryptol proof-obligation drivers beyond Rocq. |

## Rocq Driver Parity

| Rocq driver | Lean analogue | Current status | Next action |
| --- | --- | --- | --- |
| `test_arithmetic.saw` | `drivers/arithmetic/test_arithmetic.saw` | Mirrored; divide-by-zero emits through the existing `bvUDiv` primitive surface and elaborates. | Keep bitvector primitive semantics in the support-library soundness surface. |
| `test_boolean.saw` | `drivers/boolean/test_boolean.saw` | Mirrored after adding nested-op `t2` and partial-ite `t10`; focused driver elaborates and passes. | Keep under broad validation. |
| `test_lambda.saw` | `drivers/lambda/test_lambda.saw` | Mirrored. | Keep under broad validation. |
| `test_literals.saw` | `drivers/literals/test_literals.saw`; boundary in `saw-boundary/polynomial_literal_rejection` | Mostly mirrored. Octal literal now elaborates. Polynomial literal rejection is explicit because it specializes through raw-position `Prelude.error`. | Keep rejection until there is a proof-obligation design for that raw error surface. |
| `test_records.saw` | `drivers/records/test_records.saw`; module coverage in `drivers/cryptol_module_record_update` | Mirrored; direct record updates, tuple updates, relative updates, and nested-field updates elaborate and pass. | Keep under broad validation. |
| `test_sequences.saw` | `drivers/sequences/test_sequences.saw` | Mirrored; update variants, comprehension, and transpose now elaborate and pass. | Keep under broad validation. |
| `test_tuples.saw` | `drivers/tuples/test_tuples.saw` | Mirrored. | Keep under broad validation. |
| `test_typelevel.saw` | `drivers/typelevel/test_typelevel.saw` | Mirrored. | Keep under broad validation. |
| `test_offline_rocq.saw` | `drivers/offline_lean/test_offline_lean.saw` | Mirrored after adding Rocq reverse-vector and implication-chain properties; focused driver elaborates and passes. Lean also retains an extra tuple-projection proof-obligation case. | Keep under broad validation. |
| `test_prelude.saw` | `drivers/sawcore_prelude_auto_emit/test_sawcore_prelude_auto_emit.saw` | Mirrored for SAWCore Prelude emission and elaboration. | Keep as P0 validation. |
| `test_cryptol_primitives.saw` | `drivers/cryptol_primitives_auto_emit/test_cryptol_primitives_auto_emit.saw` | Mirrored; emitted Lean elaborates. | Keep under broad validation. |
| `test_cryptol_module_simple.saw` | `drivers/cryptol_module_simple/test_cryptol_module_simple.saw` | Mirrored and elaborated. | Keep under broad validation. |
| `test_cryptol_module_sha512.saw` | Partial: `drivers/cryptol_module_sha_sigma`; boundary: `saw-boundary/sha512_fix_rejection` | Not fully mirrored. Current Lean coverage isolates SHA sigma helpers and separately pins full SHA512 fix rejection. | Decide whether full SHA512 module extraction is expected to elaborate now. If not, the rejection must be user-facing and principled. |

## Lean-Only Coverage Beyond Rocq

Lean already has coverage beyond the Rocq baseline:

- proof-obligation drivers for Cryptol properties that exercise stream/fix
  helpers, running sums, popcount, and Chacha/Salsa-style examples;
- LLVM verification drivers that replace an SMT closer with `offline_lean`;
- proof harnesses that elaborate human-written Lean proofs against generated
  obligations;
- soundness boundary tests for unsupported recursors, nonproductive fix shapes,
  algebraic enums, and support-library attack probes.

These are valuable, and they point toward using Lean as a stronger replacement
for some SMT workflows. They do not close Rocq parity gaps by themselves unless
they exercise the same public feature and same semantic surface.

## Priority Order From This Matrix

1. Turn full SHA512 extraction into either an accepted elaboration test or an
   explicit boundary rejection.
3. Keep pushing emission soundness: every accepted parity case must elaborate,
   and every rejected parity case must fail at SAW translation with a diagnostic
   tied to a named soundness contract.
4. After the parity baseline is green and measurable, expand Lean-as-SMT
   replacement examples with integrated proof checking and proof-obligation
   ergonomics.
