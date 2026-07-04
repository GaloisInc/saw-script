# Example Refresh Inventory

**Date**: 2026-07-01

This inventory executes the classification phase from
`2026-07-01_example-proof-backend-refresh-goal.md`. It is deliberately not a
golden refresh log. Rows marked with an action still need follow-up before the
example corpus can be called refreshed.

## Baseline Evidence

Commands run from `deps/saw-script`:

- `make -C otherTests/saw-core-lean test`: after the E-series checkpoint,
  failed with 30 failures, all in driver/example emission surfaces. The proof
  harness rows passed, including `E3_point_commutes` and
  `point_shift_property`.
- `make -C otherTests/saw-core-lean conformance`: passed, while reporting 78
  pinned known gaps. This remains a guardrail, not a full parity claim.
- `make -C otherTests/saw-core-lean clean`: passed and removed generated
  artifacts after the exploratory runs.
- 2026-07-02 `make -C otherTests/saw-core-lean test`: reports 18 classified
  driver failures and 87 pinned known-gap/proof-gap/stress inventory rows. The
  default sweep now runs both `proofs/*` and `support-proofs/*`; every row in
  those two buckets passed. It also inventories `proof-gaps/*` and `stretch/*`
  so preserved gaps are surfaced in the test summary rather than silent skips.
- 2026-07-02 `make -C otherTests/saw-core-lean gaps`: reports every
  `proof-gaps/*` and `stretch/*` row as a tracked gap/stress item and validates
  that proof-gap directories have local `GAP.md` notes plus `source.txt`.
  From the repository root, the equivalent named target is
  `make test-saw-core-lean-gaps`.

The current full-suite failures are:

- `drivers/conformance_stream`
- `drivers/conformance_vector`
- `drivers/conformance_vector_zip`
- `drivers/cryptol_chacha20_core_iterate`
- `drivers/cryptol_chacha20_iround_zero`
- `drivers/cryptol_module_popcount`
- `drivers/cryptol_module_salsa20_q`
- `drivers/cryptol_module_simple`
- `drivers/cryptol_polymorphic_class_dict`
- `drivers/cryptol_running_sum_verify`
- `drivers/implRev4`
- `drivers/llvm_chacha20_core_verify`
- `drivers/llvm_chacha20_q_verify`
- `drivers/llvm_eq_u128_verify`
- `drivers/llvm_popcount_verify`
- `drivers/llvm_salsa20_q_verify`
- `drivers/offline_lean_popcount32`
- `drivers/sequences`

Observed failure families:

- Stale checked-obligation goldens: emitted files now use checked helpers such
  as `genWithBoundsM`, `atWithProof_checkedM`, and explicit local
  `h_bounds_obligation_`/`h_nonzero_obligation_` stubs.
- Stale proof fixtures: proof rows previously failed when the current producer
  output differed from tracked `.lean.good` artifacts. After the E-series
  checkpoint, the default proof harness rows pass; remaining failures are
  driver/emission rows.
- Real backend gaps: stream/helper construction still flows into raw
  `Stream.rec` positions, and `sequences.t18` exposes a wrapped function-result
  mismatch.
- Higher-order proof-carrying wrapper gap: `implRev4` reaches under-applied or
  over-applied checked `at` contracts and is rejected with a design diagnostic.
- Large crypto/LLVM examples expose sound obligations, but they are too large
  to treat as proof-automation targets in this phase.

## Classification Labels

Use the labels from the goal document:

- `current-proof`
- `current-emission`
- `proof-gap`
- `backend-gap`
- `boundary`
- `stress`
- `legacy-retire`

The label is the honest role for the row. The `Action` column records whether
the row is already handled or still needs refresh, reduction, or movement.

## Driver Inventory

| Path | Classification | Evidence | Linked row / blocker | Action |
| --- | --- | --- | --- | --- |
| `drivers/arithmetic` | `current-emission` | Focused driver passes after reviewed checked-obligation golden refresh. | Partial BV division/remainder and bounds obligations. | Keep as current emission coverage; do not count as proof discharge. |
| `drivers/boolean` | `current-emission` | Full suite passed. | Covered by `differential/boolean*`. | Keep. |
| `drivers/conformance_algebraic` | `current-emission` | Full suite passed. | Legacy litmus; true coverage is `differential/algebraic_control`. | Keep as smoke or retire after migration. |
| `drivers/conformance_bitvector` | `current-emission` | Focused driver passes after reviewed checked-obligation golden refresh. | True coverage split across `differential/bitvector_*`; BV proof gaps pinned. | Keep as legacy smoke; do not count as differential conformance. |
| `drivers/conformance_bitvector_conversions` | `current-emission` | Full suite passed. | `differential/bitvector_conversions`. | Keep as smoke or retire after migration. |
| `drivers/conformance_boolean` | `current-emission` | Full suite passed. | `differential/boolean*`. | Keep as smoke or retire after migration. |
| `drivers/conformance_core` | `current-emission` | Full suite passed. | `differential/core_*`. | Keep as smoke or retire after migration. |
| `drivers/conformance_error` | `current-emission` | Full suite passed. | `differential/error_unreachable`; runtime-error rows pinned. | Keep as smoke. |
| `drivers/conformance_proof_obligations` | `current-emission` | Full suite passed. | `obligations/proof_*`, `saw-boundary/proof_primitive_rejection`. | Keep as obligation smoke. |
| `drivers/conformance_record` | `current-emission` | Full suite passed. | `differential/record_*`. | Keep as smoke or retire after migration. |
| `drivers/conformance_scalar` | `current-emission` | Focused driver passes after reviewed checked-obligation golden refresh. | `differential/nat_scalar`, `int_scalar`, rational gaps. | Keep as legacy smoke; do not count as differential conformance. |
| `drivers/conformance_scalar_extra` | `current-emission` | Focused driver passes after reviewed checked-obligation golden refresh. | Scalar differential rows; literal nonzero proof support gaps. | Keep as legacy smoke; do not count as differential conformance. |
| `drivers/conformance_stream` | `backend-gap` | Lean elaboration failed: `Pure Stream`/`Bind Stream` and wrapped `MkStream` into raw `Stream.rec`. | `differential/stream_helpers`, `obligations/stream_*_totality`. | Do not refresh; needs stream/recursor design. |
| `drivers/conformance_string` | `current-emission` | Full suite passed. | `differential/string*`. | Keep as smoke or retire after migration. |
| `drivers/conformance_string_bytes` | `current-emission` | Focused driver passes after reviewed `genWithBoundsM` golden refresh. | `differential/string_bytes`. | Keep as legacy smoke; do not count as differential conformance. |
| `drivers/conformance_tuple` | `current-emission` | Full suite passed. | `differential/tuple_*`. | Keep as smoke or retire after migration. |
| `drivers/conformance_vector` | `backend-gap` | Current generated artifact still contains legacy `atWithDefaultM` fallback paths. | `differential/vector_*`, vector proof-carrying obligation rows. | Do not refresh until direct vector helper emission is migrated away from fallback/defaulting. |
| `drivers/conformance_vector_zip` | `backend-gap` | Current generated artifact still contains legacy `atWithDefaultM` fallback paths. | `differential/sequence_map_zip`, vector proof-carrying obligation rows. | Do not refresh until direct vector helper emission is migrated away from fallback/defaulting. |
| `drivers/conformance_zero_divisor_obligations` | `current-emission` | Focused driver passes after reviewed checked-obligation golden refresh. | `obligations/partial_*`, `obligations/cryptol_ec_*_zero`. | Keep as obligation smoke; do not count as proof discharge. |
| `drivers/cryptol_chacha20_core_iterate` | `stress` | Full suite failed; corresponding proof gap exists. | `proof-gaps/cryptol_chacha20_core_iterate`. | Keep as stress/proof gap; mine only small blockers. |
| `drivers/cryptol_chacha20_iround_zero` | `stress` | Full suite failed; corresponding proof gap exists. | `proof-gaps/cryptol_chacha20_iround_zero`. | Keep as stress/proof gap; mine only small blockers. |
| `drivers/cryptol_chained_projection_share` | `current-emission` | Focused driver passes after reviewed bounds-obligation golden refresh. | Bounds/projection drift only; no fallback helpers in current artifact. | Keep as current emission smoke. |
| `drivers/cryptol_module_dag_sharing` | `current-emission` | Full suite passed. | Whole-module emission smoke. | Keep. |
| `drivers/cryptol_module_enum` | `current-emission` | Focused driver passes after reviewed `genWithBoundsM` golden refresh. | Whole-module enum generation smoke; algebraic-enum gaps remain pinned separately. | Keep as current emission smoke; do not infer full algebraic-enum parity. |
| `drivers/cryptol_module_error_string` | `current-emission` | Focused driver passes after reviewed checked BV nonzero golden refresh. | Partial/error rows are pinned. | Keep as current emission smoke; source-level error paths are not fallback indexing. |
| `drivers/cryptol_module_intmod` | `current-emission` | Full suite passed. | `differential/intmod_*`. | Keep. |
| `drivers/cryptol_module_point` | `current-emission` | Focused driver passes; no current golden drift. | Record/tuple rows pass; proof counterpart separate. | Keep as current Point exercise emission smoke. |
| `drivers/cryptol_module_popcount` | `stress` | Full suite failed. | BV/proof ergonomics and large proof obligations. | Keep out of conformance; mine small blockers only. |
| `drivers/cryptol_module_rational` | `current-emission` | Focused driver passes after reviewed rational nonzero-obligation golden refresh. | `differential/rational_scalar`, partial rational obligations. | Keep as whole-module emission smoke; rational proof/library gaps remain pinned separately. |
| `drivers/cryptol_module_rec_ones` | `current-emission` | Focused driver passes; current artifact elaborates with explicit `saw_mkStream_total_exists` and `saw_fix_unique_exists` obligations. | `obligations/mkstream_total`, `obligations/fix_wrapped_unique`, stream totality rows. | Keep as proof-carrying stream/fix emission smoke. Do not count as proof discharge, and do not treat the remaining local `by sorry` obligations as solved. |
| `drivers/cryptol_module_record_update` | `current-proof` | Focused driver passes, and `proofs/point_shift_property` checks against the current emitted module. | `differential/record_update`; `proofs/point_shift_property`. | Keep as generated proof-backend example for record-update behavior. |
| `drivers/cryptol_module_salsa20_q` | `stress` | Full suite failed. | Large BV/crypto proof surface. | Keep stress; mine small blockers only. |
| `drivers/cryptol_module_sha_sigma` | `current-emission` | Full suite passed. | Crypto primitive litmus rows cover smaller gaps. | Keep as current emission smoke. |
| `drivers/cryptol_module_simple` | `current-emission` | Focused driver passes after the raw/wrapped recursor convention and reviewed golden refresh. | `differential/cryptol_vector_eq_dictionary`, `obligations/recursor_wrapped_scrutinee_function_result_error_propagates`. | Keep as target whole-module regression for wrapped dictionary recursors plus checked bounds obligations. |
| `drivers/cryptol_module_stream_fibs` | `current-emission` | Focused driver passes; current artifact elaborates with explicit stream totality and fixed-point uniqueness obligations. | `obligations/mkstream_total`, `obligations/fix_wrapped_unique`, stream totality rows. | Keep as proof-carrying stream/fix emission smoke. Do not count as proof discharge, and do not hide the remaining local proof placeholders. |
| `drivers/cryptol_polymorphic_class_dict` | `current-emission` | Focused driver passes after the raw/wrapped recursor convention. | `differential/cryptol_vector_eq_dictionary`, `obligations/recursor_wrapped_scrutinee_function_result_error_propagates`. | Keep as target whole-module regression for polymorphic class dictionaries. |
| `drivers/cryptol_primitives_auto_emit` | `current-emission` | Full suite passed. | Command-level Rocq parity. | Keep. |
| `drivers/cryptol_running_sum_verify` | `proof-gap` | Full suite failed; explicit gap note exists. | `proof-gaps/cryptol_running_sum_verify`; generic fix/proof-carrying recurrence surface. | Keep as proof gap; do not restore deleted recurrence helpers. |
| `drivers/eqBool` | `current-emission` | Full suite passed. | Small proof-obligation emission. | Keep. |
| `drivers/idBool` | `current-emission` | Full suite passed. | Small proof-obligation emission. | Keep. |
| `drivers/implRev4` | `backend-gap` | Rejected checked bounds/index contracts at non-exact arity. | Higher-order proof-carrying wrapper design gap. | Keep diagnostic; do not add raw/defaulting fallback. |
| `drivers/lambda` | `current-emission` | Full suite passed. | `differential/core_lambda`. | Keep. |
| `drivers/literalNat` | `current-emission` | Full suite passed. | Nat literal/macro emission. | Keep. |
| `drivers/literals` | `current-emission` | Full suite passed. | Literal rows. | Keep. |
| `drivers/llvm_chacha20_core_verify` | `stress` | Full suite failed with large checked bounds diffs. | Proof gap/stress; no conformance-large promotion. | Keep stress; mine small blockers only. |
| `drivers/llvm_chacha20_q_verify` | `stress` | Full suite failed; proof gap exists. | `proof-gaps/llvm_chacha20_q_eq`. | Keep stress/proof gap. |
| `drivers/llvm_eq_u128_verify` | `stress` | Full suite failed with large checked bounds diffs. | Bounds proof support, not Haskell automation. | Keep stress unless small blocker extracted. |
| `drivers/llvm_point_verify` | `current-proof` | Full suite passed; proof `llvm_point_eq` passed. | `proofs/llvm_point_eq`. | Keep as canonical proof-backend example. |
| `drivers/llvm_popcount_verify` | `stress` | Full suite failed. | BV-heavy proof obligations. | Keep stress; no `bv_decide`. |
| `drivers/llvm_salsa20_q_verify` | `stress` | Full suite failed; proof gap exists. | `proof-gaps/llvm_salsa20_q_eq`. | Keep stress/proof gap. |
| `drivers/offline_lean` | `current-proof` | Focused driver passes after reviewed `t6` golden refresh. `t1`/`t2`/`t3`/`t4`/`t5` have current proof examples; `t6` remains current emission coverage for sequence reverse with visible bounds obligations; `t7` remains a small emitted proof-obligation outline without a separate proof fixture. | `proofs/offline_t1`, `offline_t3`, `offline_t4`, `tuple_fst`, `walkthrough`; `differential/sequence_append_reverse`. | Keep. Do not count `t6`/`t7` as proof discharge unless separate proof fixtures are added and checked. |
| `drivers/offline_lean_e_series` | `current-emission` | Focused driver passes after reviewed golden refresh. E1/E2/E3/E7 pass as current proof examples; E4/E5 are explicit proof gaps; E6 remains current emission/stress coverage with fix and bounds obligations. | `proofs/E*_`; `proof-gaps/E4_map_id`, `proof-gaps/E5_littleendian`; `differential/record_projection_binder`. | Keep. Do not promote E4/E5 back into `proofs/` until their visible bounds obligations are discharged by proof-support work. |
| `drivers/offline_lean_popcount32` | `stress` | Full suite failed; explicit gap note exists. | `proof-gaps/offline_lean_popcount32`; BV-heavy popcount proof surface. | Keep stress/proof gap; no native-eval proof shortcuts. |
| `drivers/records` | `current-emission` | Full suite passed. | `differential/record_*`. | Keep. |
| `drivers/sawcore_prelude_auto_emit` | `current-emission` | Focused driver passes after recursor motive-shape fix; no golden refresh needed. | Prelude auto-emit convention; opaque type-family motives stay raw. | Keep as regression for higher-sort recursor motives. |
| `drivers/sequences` | `backend-gap` | Stale bounds diffs plus `t18` higher-order wrapped-function application failure in `foldl (+)`. | `differential/sequence_*`, branch/derived-bounds gaps. | Do not refresh failing row until the `foldl (+)` function-adapter gap is reduced/design-linked. |
| `drivers/tuples` | `current-emission` | Full suite passed. | `differential/tuple_*`. | Keep. |
| `drivers/typelevel` | `current-emission` | Full suite passed. | Sort/typelevel differential rows. | Keep. |

## Proof Inventory

| Path | Classification | Evidence | Linked source | Action |
| --- | --- | --- | --- | --- |
| `proofs/E1_bvAdd_comm` | `current-proof` | Proof passed axiom audit. | `drivers/offline_lean_e_series/E1`. | Keep. |
| `proofs/E2_iteDep_refl` | `current-proof` | Proof passed axiom audit. | `drivers/offline_lean_e_series/E2`. | Keep. |
| `proofs/E3_point_commutes` | `current-proof` | Proof passed after the record-projection binder shape bug was reduced to and fixed under `differential/record_projection_binder`. | `drivers/offline_lean_e_series/E3`. | Keep. |
| `proofs/E7_wide_assoc` | `current-proof` | Proof passed axiom audit. | `drivers/offline_lean_e_series/E7`. | Keep. |
| `proofs/completed_outline_smoke` | `current-proof` | Proof passed axiom audit against generated-outline fixture. | `drivers/offline_lean/t1`. | Keep as harness smoke. |
| `proofs/llvm_point_eq` | `current-proof` | Proof passed axiom audit. | `drivers/llvm_point_verify`. | Keep as canonical end-to-end proof example. |
| `proofs/offline_t1` | `current-proof` | Proof passed axiom audit. | `drivers/offline_lean/t1`. | Keep. |
| `proofs/offline_t3` | `current-proof` | Proof passed axiom audit. | `drivers/offline_lean/t3`. | Keep. |
| `proofs/offline_t4` | `current-proof` | Proof passed axiom audit. | `drivers/offline_lean/t4`. | Keep. |
| `proofs/point_shift_property` | `current-proof` | Focused proof harness passes against the current emitted `drivers/cryptol_module_record_update` module. | `drivers/cryptol_module_record_update`. | Keep as generated proof-backend example for record-update behavior. |
| `proofs/tuple_fst` | `current-proof` | Proof passed axiom audit. | `drivers/offline_lean/t5`. | Keep. |
| `proofs/walkthrough` | `current-proof` | Proof passed axiom audit. | `drivers/offline_lean/t2`. | Keep. |

## Support-Proof Inventory

These rows run in the default test sweep but are deliberately outside
`proofs/`, because they are Lean support-library regressions rather than
generated proof-backend discharge examples.

| Path | Classification | Evidence | Linked source | Action |
| --- | --- | --- | --- | --- |
| `support-proofs/conformance_algebraic` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_bitvector` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_bitvector_conversions` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_boolean` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_core` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_error` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_record` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_scalar` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_scalar_extra` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_stream` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_string` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_string_bytes` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_tuple` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_vector` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/conformance_vector_zip` | `legacy-retire` | Lean support proof passed, but not a generated proof-backend example. | Legacy conformance driver. | Keep as support regression only; do not count as proof discharge. |
| `support-proofs/cookbook` | `legacy-retire` | Pins support-library cookbook patterns, not emitted proof artifacts. | `doc/proof-cookbook.md`. | Keep as support-library doc test; do not count as proof discharge. |

## Proof-Gap Inventory

| Path | Classification | Evidence | Linked source | Action |
| --- | --- | --- | --- | --- |
| `proof-gaps/cryptol_chacha20_core_iterate` | `proof-gap` | Explicit local gap note; large crypto proof attempt exceeds practical checked-proof budget. | `drivers/cryptol_chacha20_core_iterate`. | Keep pinned; no native-eval proof shortcut or heartbeat-only promotion. |
| `proof-gaps/cryptol_chacha20_iround_zero` | `proof-gap` | Explicit local gap note; large crypto recurrence proof attempt exceeds practical checked-proof budget. | `drivers/cryptol_chacha20_iround_zero`. | Keep pinned; no native-eval proof shortcut or heartbeat-only promotion. |
| `proof-gaps/cryptol_running_sum_verify` | `proof-gap` | Explicit gap note for the small recurrence proof. | `drivers/cryptol_running_sum_verify`. | Keep pinned; close through later proof-support work for recurrence and bounds obligations. |
| `proof-gaps/E4_map_id` | `proof-gap` | Small E-series proof now blocked only by visible checked bounds obligations. | `drivers/offline_lean_e_series/E4`. | Keep out of the default proof harness until proof-support work closes the obligations. |
| `proof-gaps/E5_littleendian` | `proof-gap` | Small E-series proof now blocked by visible checked bounds obligations over reverse/indexing. | `drivers/offline_lean_e_series/E5`. | Keep out of the default proof harness until proof-support work closes the obligations. |
| `proof-gaps/llvm_chacha20_q_eq` | `proof-gap` | Explicit local gap note; preserved proof attempt still uses `bv_decide` for quarterround BV equations. | `drivers/llvm_chacha20_q_verify`. | Keep pinned; mine only minimal blockers and do not promote while it depends on native-evaluation proof artifacts. |
| `proof-gaps/llvm_salsa20_q_eq` | `proof-gap` | Explicit local gap note; preserved proof attempt still uses `bv_decide` for the final Salsa20 BV identity. | `drivers/llvm_salsa20_q_verify`. | Keep pinned; mine only minimal blockers and do not promote while it depends on native-evaluation proof artifacts. |
| `proof-gaps/offline_lean_popcount32` | `proof-gap` | Explicit gap note for the width-32 popcount recurrence proof. | `drivers/offline_lean_popcount32`. | Keep pinned as stress/proof gap; no native proof shortcuts. |

## Stretch Inventory

| Path | Classification | Evidence | Linked row / blocker | Action |
| --- | --- | --- | --- | --- |
| `stretch/sha512_full_module_probe` | `stress` | Explicit stretch directory, excluded from default test sweep. | SHA512/full-module scalability, not Rocq parity gate. | Keep as stretch; mine smaller blockers only. |

## Documentation Examples

| Path | Classification | Evidence | Action |
| --- | --- | --- | --- |
| `doc/proof-cookbook.md` | `legacy-retire` | Covered by `support-proofs/cookbook`, but this is support-library proof guidance, not generated proof-backend replay. | Keep useful content, but do not count as current proof-backend success until examples import generated artifacts. |
| `doc/getting-started.md` | `current-proof` | Covered by `proofs/walkthrough`, which imports the generated `Emitted` artifact. | Keep in current-proof set. |

## Refresh Review Log

### `drivers/offline_lean_e_series`

Commands:

```sh
SAW=... bash ../../support/lean-driver-test.sh good
SAW=... bash ../../support/lean-driver-test.sh test
```

Reviewed result:

- `E3` stopped diffing after the backend recursor shape fix pinned by
  `differential/record_projection_binder`.
- `E4`, `E5`, and `E6` goldens were refreshed to the current proof-carrying
  emission. The substantive drift is from unchecked/default vector helpers
  (`genM`, `atWithDefaultM`) to checked helpers (`genWithBoundsM`,
  `atWithProof_checkedM`) and visible bounds/fix obligations.
- The refresh did not restore fallback/defaulting behavior, add Haskell
  arithmetic proof search, or add Lean automation to make the old proofs pass.

### `drivers/offline_lean`

Commands:

```sh
SAW=... bash ../../support/lean-driver-test.sh good
SAW=... bash ../../support/lean-driver-test.sh test
```

Reviewed result:

- Only `t6` drifted. The new artifact replaces unchecked/default sequence
  indexing (`genM`, `atWithDefaultM`, and `saw_throw_error` fallback values)
  with `genWithBoundsM`, `atWithProof_checkedM`, and visible local
  `h_bounds_` obligations.
- This is the expected proof-carrying bounds shape for the reverse-of-two
  sequence property. It is current emission coverage, not proof discharge:
  no separate proof fixture currently closes these bounds obligations.
- The refresh did not add Haskell-side bounds reasoning, restore defaulting
  behavior, or add Lean automation to make the obligation discharge.

### `drivers/arithmetic`

Commands:

```sh
SAW=... bash ../../support/lean-driver-test.sh good
SAW=... bash ../../support/lean-driver-test.sh test
```

Reviewed result:

- Only `t2`, `t3`, `t4`, `t11`, and `t12` drifted. The division/remainder rows
  now emit `bvNonzeroM` obligations and checked `bvUDiv_checkedM` /
  `bvURem_checkedM` calls. The extension rows now use `genWithBoundsM`,
  `atWithProof_checkedM`, and visible local `h_bounds_` obligations.
- The refresh removes old unchecked/defaulting artifacts from the goldens:
  `atWithDefaultM`, `saw_throw_error` fallback values, and older
  `bv*Checked`-with-bound-divisor shapes are no longer the reviewed baseline.
- This is current emission coverage only. The generated local obligations are
  intentionally visible and are not automatically discharged by backend-added
  proof automation.

### Small `drivers/conformance_*` Current-Emission Refreshes

Commands:

```sh
SAW=... bash ../../support/lean-driver-test.sh good
SAW=... bash ../../support/lean-driver-test.sh test
```

Reviewed result:

- Refreshed `conformance_bitvector`, `conformance_scalar`,
  `conformance_scalar_extra`, `conformance_string_bytes`, and
  `conformance_zero_divisor_obligations` after focused review.
- The refreshed artifacts contain the expected checked-obligation shapes:
  `genWithBoundsM`, `atWithProof_checkedM`, checked nonzero/division helpers,
  and visible local `h_bounds_` / `h_nonzero_` obligations.
- The generated artifacts selected for refresh were checked for old
  fallback/defaulting helpers such as `atWithDefaultM`, unchecked
  `*Checked` helpers, `ratioChecked`, and `saw_throw_error` fallbacks.
- `conformance_vector` and `conformance_vector_zip` were not refreshed. Their
  current generated artifacts still contain legacy `atWithDefaultM` fallback
  paths, so they are backend gaps for the direct vector-helper migration rather
  than valid current-emission goldens.

### Small Whole-Module/Projection Refreshes

Commands:

```sh
SAW=... bash ../../support/lean-driver-test.sh good
SAW=... bash ../../support/lean-driver-test.sh test
```

Reviewed result:

- Refreshed `cryptol_chained_projection_share`, `cryptol_module_enum`, and
  `cryptol_module_error_string` after focused review.
- `cryptol_chained_projection_share` drifted from unchecked/default indexing
  to `genWithBoundsM`, `atWithProof_checkedM`, and local bounds obligations.
- `cryptol_module_enum` drifted only from `genM` to `genWithBoundsM`; this is
  current whole-module emission smoke, not evidence that the separately pinned
  algebraic-enum/ListSort gaps are closed.
- `cryptol_module_error_string` drifted from an old checked-divisor shape to
  `bvNonzeroM` plus `bvUDiv_checkedM`. The remaining `saw_throw_error`
  occurrences in the module are source-level error behavior, not the removed
  index-default fallback.
- `cryptol_module_rational` drifted from `ratioChecked` with a bound raw
  divisor to `ratio_checkedM` plus a visible checked nonzero obligation. This
  keeps the whole-module rational smoke current without claiming proof-library
  coverage for nontrivial rational arithmetic.

### `drivers/sawcore_prelude_auto_emit`

Commands:

```sh
cabal build exe:saw
SAW=... bash ../../support/lean-driver-test.sh test
```

Reviewed result:

- The generated prelude probe temporarily exposed a real backend bug:
  `Eq__rec` emitted `Pure.pure (@Eq.rec ...)`, which is ill-typed because the
  motive is an opaque type family over `Sort`, not a value-domain motive.
- The backend fix is a general shape predicate for variable-headed type
  families whose type is a Pi returning `Sort`. Such opaque motives now stay
  raw; explicit value-domain motives still use the wrapped convention.
- Focused `sawcore_prelude_auto_emit`, `offline_lean_e_series`, and
  `differential/record_projection_binder` tests passed after the fix.

## Required Follow-Up Before Completion

2026-07-01 full-harness checkpoint after the reviewed refreshes and recursor
motive fix: `make -C otherTests/saw-core-lean test` reports 18 remaining
failures. The remaining failing rows are now classified blockers rather than
unreviewed safe refreshes:

- P0 raw/wrapped recursor and dictionary convention:
  `cryptol_module_simple`, `cryptol_polymorphic_class_dict`,
  and `differential/cryptol_vector_eq_dictionary` are now promoted by the
  2026-07-02 recursor checkpoint. `conformance_stream` / `stream_helpers` and
  `sequences.t18` remain separate stream-recursion and higher-order function
  adapter gaps.
- P1 higher-order value-function convention:
  `sequences.t18`, with focused litmus coverage in `differential/vector_fold`
  and `differential/cryptol_ec_fold_scan`. This is the next backend target
  because it is an ordinary value-function wrapping convention, not proof
  automation.
- P2 direct vector fallback/defaulting review:
  `conformance_vector`, `conformance_vector_zip` only after reducing any
  remaining broad-driver failure to a focused litmus row. Current conformance
  documentation records positive focused coverage for `genM`/`foldrM`/`foldlM`
  wrapper adaptation and equal-length `zip`, so do not chase the older broad
  classification without a fresh reduction.
- P3 higher-order proof-carrying/indexing gap: `implRev4`.
- P4 recurrence/proof-obligation gaps: `cryptol_running_sum_verify`.
- P5 large/stress examples: Chacha/Salsa/LLVM/popcount rows and
  `offline_lean_popcount32`.
- Mixed stale-plus-real sequence gap: `sequences`, blocked by `t18`; the live
  blocker is now classified as higher-order wrapped-function application around
  `foldl (+)`, not the dictionary recursor convention.

1. The wrapped dictionary/record-rec gap exposed by `cryptol_module_simple`
   and `cryptol_polymorphic_class_dict` is closed by the 2026-07-02
   raw/wrapped recursor convention. The implementation binds a wrapped
   scrutinee, runs the raw recursor inside the continuation, and preserves the
   surrounding expected shape, including value-producing function recursors.
   Do not rawify dictionaries or add fixture-specific record
   recursor code. See
   `doc/2026-07-02_raw-wrapped-recursor-dictionary-plan.md`.
2. Review and refresh only the small stale proof-backend goldens whose new
   emission is the expected proof-carrying shape:
   the remaining whole-module or sequence driver goldens are first candidates.
   `arithmetic`, `offline_lean`, `offline_lean_e_series`, and the safe small
   conformance-style driver goldens have focused reviewed refreshes.
3. Completed: `point_shift_property` and its producer
   `drivers/cryptol_module_record_update` both pass focused tests against the
   current emitted artifact; keep this as a current proof-backend example. `E3`
   is repaired and `E4`/`E5` are explicit proof gaps.
4. Do not refresh `conformance_stream`, `sequences.t18`, `implRev4`, or large
   crypto/LLVM examples as a way to make the harness green. Each currently
   points at a real backend/design/proof-ergonomics blocker. The stream module
   examples `cryptol_module_rec_ones` and `cryptol_module_stream_fibs` are
   already classified as current emission smoke only; they still expose local
   stream/fix obligations and are not proof-discharge successes.
5. Completed: legacy support-library proof rows moved from
   `proofs/conformance_*` and `proofs/cookbook` to `support-proofs/*`, which
   runs in the default sweep while keeping `proofs/` reserved for generated
   proof-backend examples.
6. After reviewed refreshes and movements, rerun:

```sh
make -C otherTests/saw-core-lean test
make -C otherTests/saw-core-lean conformance
make -C otherTests/saw-core-lean gaps
make test-saw-core-lean-gaps
make -C otherTests/saw-core-lean clean
```

The refresh goal is not complete until the default full harness no longer fails
because of unexplained stale artifacts, and every remaining non-green item is
surfaced as a proof gap, backend gap, boundary, stress item, or retired legacy
row.
