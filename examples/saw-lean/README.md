# saw-lean-example

End-to-end demo of SAW's Lean 4 backend. Mirrors the layout of the
neighbouring `saw-rocq-example/`. The same `rev.cry` module drives
both. This directory exercises the three primary commands the
backend exposes:

- `write_lean_term` — translate a single SAWCore term to a `.lean`.
- `write_lean_cryptol_module` — translate every Cryptol top-level
  in a `.cry` source into a `namespace <Mod>` block of `def`s.
- `offline_lean` — punt a SAWScript proof obligation to Lean as a
  `theorem goal : <Prop> := by sorry` stub the user can open and
  discharge.

## Files

- `rev.cry` — Cryptol source. Three definitions (`idBool`, `implRev`
  — a polymorphic reverse, `specRev` — its spec) and two `property`
  declarations (`revInvolutive`, `impl_eq_spec`).
- `demo.saw` — the SAWScript driver. Translates two monomorphic
  instances, the whole module, and both properties.
- `out/` — generated `.lean` files (gitignored).
- `proof/Makefile` — invokes Lean on the discharged proofs in
  `proof/{invol,eq}/`. Each subdirectory pairs the `Emitted.lean`
  copied from `out/` with a hand-written `proof.lean` that closes
  the goal.

## Running the SAW driver

```bash
cd examples/saw-lean
../../dist-newstyle/build/<host-triple>/ghc-<v>/saw-<v>/x/saw/build/saw/saw demo.saw
```

The `out/` directory is created automatically by `write_lean_term`
/ `write_lean_cryptol_module` / `offline_lean`.

`saw` writes:

```
out/
├── idBool.lean         # \(b : Bit) -> b           via write_lean_term
├── implRev.lean        # implRev`{4,[8]}           via write_lean_term
├── Rev.lean            # whole rev.cry             via write_lean_cryptol_module
├── invol_prove0.lean   # revInvolutive proof goal  via offline_lean
└── eq_spec_prove0.lean # impl_eq_spec proof goal   via offline_lean
```

Every file imports `CryptolToLean` and elaborates against the support
library shipped with `saw-core-lean/lean/`. The `_prove0.lean` files
contain a `theorem goal : <Prop> := by sorry` stub.

## Discharging the property goals

The `proof/` directory holds completed discharges for the two
`offline_lean` goals. To rebuild and check both:

```bash
cd examples/saw-lean/proof
make invol  # discharges revInvolutive
make eq     # discharges impl_eq_spec
```

Each target compiles `Emitted.lean` (a copy of the corresponding
`out/*_prove0.lean`), then elaborates `proof.lean`, which `import`s
the emitted `.olean` and closes the goal. The Makefile picks up the
support library from `../../../saw-core-lean/lean/.lake/`, so
`lake build` must have run there at least once.

To regenerate the `Emitted.lean` files after editing `rev.cry` or
`demo.saw`:

```bash
cd examples/saw-lean
mkdir -p out
saw demo.saw
cp out/invol_prove0.lean   proof/invol/Emitted.lean
cp out/eq_spec_prove0.lean proof/eq/Emitted.lean
```

## Why this exists

`examples/saw-lean/` is *demo-as-documentation*, not a regression
suite — `otherTests/saw-core-lean/` is the regression suite. Use
this directory when you want to (a) hand-walk the end-to-end SAW →
Lean → discharge story, or (b) sanity-check that a backend change
hasn't broken the surface for new users.
