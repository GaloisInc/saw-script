# saw-lean example

End-to-end demo of SAW's Lean 4 backend, driven by `rev.cry`
(reverse, its spec, and two properties). This is the CANONICAL copy
(the untracked `saw-lean-example/` folder in the parent workspace is
legacy); `saw-core-lean/doc/getting-started.md` walks this flow.

> **STATUS 2026-07-18 (post recursor-convention + wrapper arc)**
>
> - `write_lean_term` steps work; `out/{idBool,implRev}.lean`
>   regenerate and elaborate.
> - Step 3b: the reduced module (`rev_impl.cry`, implRev alone)
>   TRANSLATES AND ELABORATES — `out/Rev.lean` is produced for real
>   (the 0.02 rev.cry criterion; differential pin:
>   `otherTests/saw-core-lean/differential/cryptol_rev_module`).
>   The FULL module (step 3) still rejects at `specRev`'s built-in
>   `reverse` → raw-position `Prelude.error` (audited 2026-07-14
>   disposition) and stays `fails`-wrapped.
> - `offline_lean` is emission-only (goals stay unsolved; the
>   Lean-side discharges live in `proof/Proofs/{Invol,Eq}.lean`).
>   SAW-side replay (`offline_lean_replay`) is WIRED IN as demo
>   step 5: SAW re-emits each goal fresh, checks
>   `proof/replay/{invol,eq}/proof.lean` under the factored trust
>   kernel, and SOLVES both goals on Lean's kernel authority (not
>   `fails`-wrapped). What that does and does not establish —
>   mistakes-not-malice, and why `LeanReplayEvidence` produced by
>   someone else is a claim to re-establish by re-running replay
>   yourself — is the threat-model section of
>   `saw-core-lean/README.md`; read it before handing replay
>   results to a second party.
>   *(Blockquote verified current 2026-07-30, wave-4 demo audit:
>   the committed Emitted copies are token-identical to fresh
>   emission at HEAD.)*

- `write_lean_term` — translate a single SAWCore term to a `.lean`.
- `write_lean_cryptol_module` — translate every Cryptol top-level
  in a `.cry` source into a `namespace <Mod>` block of `def`s.
- `offline_lean` — punt a SAWScript proof obligation to Lean as a
  `noncomputable def goal : Prop := <Prop>` plus a
  `theorem goal_holds : goal := by sorry` stub the user can open and
  discharge. EMISSION-ONLY: the goal is left unsolved on the SAW
  side (`demo.saw` wraps each `prove_print` in `fails`); SAW never
  claims a goal on the strength of an export.

## Files

- `rev.cry` — Cryptol source. Two definitions (`implRev` — a
  polymorphic reverse, `specRev` — its spec) and three `property`
  declarations (`revInvolutive`, `impl_eq_spec`, `sum_example`).
  (`idBool` is a SAWScript `let` in `demo.saw`, not a Cryptol
  definition.)
- `rev_impl.cry` — the reduced module (`implRev` alone) that step
  3b translates whole; deleting it breaks `demo.saw`.
- `demo.saw` — the SAWScript driver. Translates two monomorphic
  instances and both properties; the FULL-module step is a
  documented release-0.01 rejection (wrapped in `fails`, see below).
- `depanalysis.saw` — a standalone dependency-analysis driver
  (`enable_experimental` + `normalize_term`); run it the same way
  as `demo.saw`. Not exercised by `demo.saw`.
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
SAW_LEAN_ROOT=$(cd ../.. && pwd) \
  ../../dist-newstyle/build/<host-triple>/ghc-<v>/saw-<v>/x/saw/build/saw/saw demo.saw
```

`SAW_LEAN_ROOT` is REQUIRED for this invocation: the demo's replay
steps (5) resolve the trust-kernel assets through it, and a
dist-newstyle build's compiled-in data directory points at an
uninstalled path — without the variable the run emits everything
and then aborts at step 5. Point it at the checkout root (as
above); from an unpacked release tarball, the tarball root works
the same way (it ships `saw-core-lean/{lean,replay}`). Note the
replay steps build the support library in `saw-core-lean/lean` —
see the Step 3 warning below.

The `out/` directory is created automatically. `saw` writes:

```
out/
├── idBool.lean         # \(b : Bit) -> b           via write_lean_term
├── implRev.lean        # implRev`{4,[8]}           via write_lean_term
├── Rev.lean            # reduced module (implRev)  via write_lean_cryptol_module
├── invol_prove0.lean   # revInvolutive proof goal  via offline_lean
└── eq_spec_prove0.lean # impl_eq_spec proof goal   via offline_lean
```

`out/Rev.lean` IS produced (since 2026-07-18): the reduced module
(implRev alone) translates and elaborates, un-`fails`-wrapped —
differentially pinned by
`otherTests/saw-core-lean/differential/cryptol_rev_module`. Only
the FULL module (`out/RevFull.lean`) still rejects at SAW
translation time: `specRev`'s built-in `reverse` reaches
`Prelude.error` demanded at a raw position (the audited raw-error
disposition), so `demo.saw` wraps that one step in `fails`. The two
`prove_print (offline_lean …)` steps are likewise `fails`-wrapped
because emission leaves the goals unsolved by design.

Every file imports `CryptolToLean` and elaborates against the
support library shipped with `saw-core-lean/lean/`. The
`_prove0.lean` files contain a `noncomputable def goal : <Prop>` +
a placeholder `theorem goal_holds : goal := by sorry`.

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
SAW_LEAN_ROOT=$(cd ../.. && pwd) saw demo.saw
# Paste out/invol_prove0.lean into proof/Proofs/InvolEmitted.lean
# (keeping the `namespace InvolDemo` / `end InvolDemo` wrapper).
# Similarly for out/eq_spec_prove0.lean → proof/Proofs/EqEmitted.lean.
```

### Step 3 — Discharge via `lake build`

> **WARNING (shared-tree toolchain clobber).** This project pins
> Lean `v4.29.1` (`proof/lean-toolchain`) while the shared support
> library at `saw-core-lean/lean` pins `v4.32.0` — and the
> `require` below builds that shared library IN PLACE. Running this
> step (or Step 1's replay, which builds the same tree at 4.32.0)
> inside a dev checkout leaves the library's build products at
> whichever toolchain ran last; harnesses that consume the existing
> build without rebuilding then fail with "incompatible header"
> errors that read like translator regressions. Recovery is one
> `lake build` in `saw-core-lean/lean`. Avoid running this step
> concurrently with the test suites. (Tracked in
> `saw-core-lean/TODO.md`; the pins should converge.)

```bash
cd examples/saw-lean/proof
lake build
```

Lake resolves the `require "cryptol_to_lean" path = "..."` in
`proof/lakefile.toml` to the support library at
`../../../saw-core-lean/lean/` (three levels up from `proof/`),
builds it, then elaborates `Proofs/Invol.lean` and
`Proofs/Eq.lean`. If either discharge fails, `lake build` fails —
there is no separate proof-check step.

## Why this exists

`examples/saw-lean/` is *demo-as-documentation*, not a regression
suite — `otherTests/saw-core-lean/` is the regression suite. Use
this directory when you want to (a) hand-walk the end-to-end SAW →
Lean → discharge story, or (b) sanity-check that a backend change
hasn't broken the surface for new users. The `proof/` Lake project
is the canonical "how should my own project import saw-core-lean"
pattern — the same `require` line works verbatim outside this
checkout with an absolute path substituted for
`../../../saw-core-lean/lean`.
