# saw-core-lean test tree — what lives where

One directory per test row; `test.sh` iterates categories in a fixed
order (see its header for harness mechanics). This README is the
taxonomy: what each category MEANS and where a new row goes.
Release 0.01 posture: every row is green, a pinned known gap, or an
expected rejection — nothing is silently red.

| Category | Meaning | A new row goes here when… |
|---|---|---|
| `workflows/` | **The release story**: SAWScript verification workflows driven end-to-end — `llvm_verify`/`prove_print` scripts that punt goals through `offline_lean` (emission-only) with the Lean discharge tracked in `proofs/` or the gap documented in `proof-gaps/`. | …it demonstrates how a USER discharges SAW proof obligations in Lean. |
| `differential/` | True executable conformance: run SAW on a litmus, run Lean on the emitted artifact, mechanically compare observed outputs. The only positive category that counts as semantic conformance. | …you can observe the same value on both sides. |
| `obligations/` | Emitted-obligation SHAPE pins: the artifact must contain the required visible contract (`contains:`/`absent:` directives) and elaborate. | …the point is what the emission looks like, not what it evaluates to. |
| `saw-boundary/` | Expected rejections: `.expect-fail` rows pinning named diagnostics at the fragment's edge. | …the input is out of fragment and must refuse loudly. |
| `drivers/` | Golden + elaboration pins for translation families: module translation (`cryptol_module_*`), auto-emission (`*_auto_emit`), and emission-surface litmus (arithmetic, records, sequences, …). | …you're pinning translator output shape for a surface, without an executable comparison or workflow framing. |
| `proofs/` | Completed Lean discharges of emitted goals (sorry-free, axiom-audited every run). | …a workflow/driver goal has a real proof. |
| `proof-gaps/` | Documented undischargeable or parked proofs (GAP.md states exactly why and what unblocks it). | …the obligation emits but cannot honestly be closed yet. |
| `support-proofs/` | Standalone proofs ABOUT the Lean support library's realizations (no SAW run). | …you're verifying library semantics, not emission. |
| `attacks/` | Hand-rolled NEGATIVE probes (`*.shouldfail.lean`) that must FAIL elaboration — soundness attacks on the support library. | …you're pinning that a malicious/wrong shape is rejected by Lean. |
| `stretch/` | Large stress probes excluded from default gates. | …it's scalability evidence, not a fence. |
| `support/` | The harness scripts themselves. | — |

Choosing `drivers/` vs `obligations/` for an emission pin: use a
DRIVER row when full byte-shape stability of the family matters
(goldens over every artifact + the SAW log — catches any drift, at
golden-refresh cost); use an OBLIGATIONS row when only the visible
contract matters (`contains:`/`absent:` directives — survives benign
drift, pins exactly the load-bearing lines).

History note (2026-07-15 restructure): `workflows/` was split out of
`drivers/`; the negative-probe category was renamed `shape/` →
`attacks/`; the pre-differential-era `drivers/conformance_*` litmus
family was dispositioned row-by-row (retired where coverage was
duplicated, migrated where unique — see the release audit's
execution record). `doc/archive/` docs cite pre-restructure paths;
they are era-accurate history, not link rot.
