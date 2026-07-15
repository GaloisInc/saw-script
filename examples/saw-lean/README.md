# saw-lean-example

End-to-end demo of SAW's Lean 4 backend. Mirrors the layout of the
neighbouring `saw-rocq-example/`. The same `rev.cry` module drives
both. This directory exercises the three primary commands the
backend exposes:

- `write_lean_term` — translate a single SAWCore term to a `.lean`.
- `write_lean_cryptol_module` — translate every Cryptol top-level
  in a `.cry` source into a `namespace <Mod>` block of `def`s.
- `offline_lean` — punt a SAWScript proof obligation to Lean as a
  `def goal : Prop := <Prop>` plus a
  `theorem goal_holds : goal := by sorry` stub the user can open and
  discharge. EMISSION-ONLY: the goal is left unsolved on the SAW
  side (`demo.saw` wraps each `prove_print` in `fails`); SAW never
  claims a goal on the strength of an export.

## Files

- `rev.cry` — Cryptol source. Three definitions (`idBool`, `implRev`
  — a polymorphic reverse, `specRev` — its spec) and two `property`
  declarations (`revInvolutive`, `impl_eq_spec`).
- `demo.saw` — the SAWScript driver. Translates two monomorphic
  instances and both properties; the whole-module step is a
  documented release-0.01 rejection (wrapped in `fails`, see below).
- `out/` — generated `.lean` files (gitignored).
- `proof/` — a small Lake project that `require`s the saw-core-lean
  support library via relative path and discharges the two emitted
  goals. Editing the proofs or re-copying Emitted files (see below)
  and running `lake build` type-checks everything end-to-end.

## Workflow: write a driver, emit, discharge

The full loop has three steps. The `proof/` subdirectory is a
runnable instance of steps 2–3.

### Step 1 — Run the SAW driver

```bash
cd examples/saw-lean
../../dist-newstyle/build/<host-triple>/ghc-<v>/saw-<v>/x/saw/build/saw/saw demo.saw
```

The `out/` directory is created automatically. `saw` writes:

```
out/
├── idBool.lean         # \(b : Bit) -> b           via write_lean_term
├── implRev.lean        # implRev`{4,[8]}           via write_lean_term
├── invol_prove0.lean   # revInvolutive proof goal  via offline_lean
└── eq_spec_prove0.lean # impl_eq_spec proof goal   via offline_lean
```

`out/Rev.lean` is NOT produced: whole-module translation of
`rev.cry` rejects at SAW translation time — `specRev`'s built-in
`reverse` reaches `Prelude.error` demanded at a raw position (the
audited raw-error disposition), and the reduced module (implRev
alone) rejects at `Prelude::Either@core`, pinned by
`otherTests/saw-core-lean/saw-boundary/polymorphic_seq_module_rejection`.
`demo.saw` wraps the step in `fails` so the run completes; the two
`prove_print (offline_lean …)` steps are likewise `fails`-wrapped
because emission leaves the goals unsolved by design.

Every file imports `CryptolToLean` and elaborates against the
support library shipped with `saw-core-lean/lean/`. The
`_prove0.lean` files contain a `def goal : <Prop>` + a placeholder
`theorem goal_holds : goal := by sorry`.

### Step 2 — Copy emitted goals into the Lake project

`proof/Proofs/InvolEmitted.lean` and `proof/Proofs/EqEmitted.lean`
are the goal stubs for step 3 to discharge. They are verbatim
copies of the SAW-emitted files with two tweaks:

- wrapped in `namespace InvolDemo` / `namespace EqDemo` so both
  `goal`s can co-exist in one Lake build, and
- the `theorem goal_holds := by sorry` stub is omitted — the
  real discharge lives in `proof/Proofs/{Invol,Eq}.lean`.

To regenerate after editing `rev.cry` / `demo.saw`:

```bash
cd examples/saw-lean
saw demo.saw
# Paste out/invol_prove0.lean into proof/Proofs/InvolEmitted.lean
# (keeping the `namespace InvolDemo` / `end InvolDemo` wrapper).
# Similarly for out/eq_spec_prove0.lean → proof/Proofs/EqEmitted.lean.
```

### Step 3 — Discharge via `lake build`

```bash
cd examples/saw-lean/proof
lake build
```

Lake resolves the `require "cryptol_to_lean" path = "..."` in
`proof/lakefile.toml` to the support library at
`../../saw-core-lean/lean/`, builds it, then elaborates
`Proofs/Invol.lean` and `Proofs/Eq.lean`. If either discharge
fails, `lake build` fails — there is no separate proof-check step.

## Why this exists

`examples/saw-lean/` is *demo-as-documentation*, not a regression
suite — `otherTests/saw-core-lean/` is the regression suite. Use
this directory when you want to (a) hand-walk the end-to-end SAW →
Lean → discharge story, or (b) sanity-check that a backend change
hasn't broken the surface for new users. The `proof/` Lake project
is the canonical "how should my own project import saw-core-lean"
pattern — the same `require` line works verbatim outside this
checkout with an absolute path substituted for `../../saw-core-lean/lean`.
