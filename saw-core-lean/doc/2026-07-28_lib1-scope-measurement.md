# LIB-1 scope measurement (2026-07-28)

Measurement backing the LIB-1 interim-fix decision (TODO.md; audit
report `doc/2026-07-24_soundness-audit-2.md` §LIB-1/D-1). Method and
numbers first, the strategic finding at the end — it changes the
option space.

## Method

Census over the 350-artifact emitted-Lean baseline
(`.snapshots/op2-baseline`, re-cut same day after a fully green
`make test`). Two passes:

1. **Co-occurrence** (upper bound): artifact contains any collapsing
   helper AND any throwing helper, anywhere.
2. **Structural** (the number that matters): a throwing helper
   INSIDE an element position of a collapsing helper — the
   `(fun …)` element-function argument of `genWithBoundsM`/`genM`/
   `foldrM`/`foldlM`, the `#v[…]` element literal of `vecSequenceM`,
   the bound-value argument of `sawLet`. Span extraction by
   paren/bracket balancing (scratch script
   `element_nesting.py`; approximates the translator-side syntactic
   analysis a rejection gate would run).

Throwing helpers = every `Except.error`/`throw` producer in the
support library: `saw_throw_error`, `atRuntimeCheckedM`, the
`*_runtimeM` division/ratio family (`divNat`/`modNat`/`divModNat`/
`intDiv`/`intMod`/`bvUDiv`/`bvURem`/`bvSDiv`/`bvSRem`/`ecSDiv`/
`ecSMod`/`ratio`/`rationalRecip`).

## Numbers

| measure | artifacts (of 350) |
|---|---|
| any collapsing helper | 172 |
| any throwing helper | 66 |
| co-occurrence (upper bound) | 62 |
| **thrower inside an element position** | **59** |

Per surface, structural hits:

| surface | artifacts | thrower breakdown |
|---|---|---|
| `genWithBoundsM` | 59 | 57 × `atRuntimeCheckedM`; 1 × `saw_throw_error` (the LIB-1 pin row itself); `cryptol_rev_module` additionally `intDiv_runtimeM`/`intMod_runtimeM`; `fix_error_elem` (error deliberately REACHED) |
| `vecSequenceM` | 2 | the LIB-1 pin row; `bitvector_order_width` (`atRuntimeCheckedM` in a literal element) |
| `foldrM` | 0 | used in 28 artifacts, never with a thrower inside the folded function |
| `foldlM` | 0 | used in 6 artifacts, same |
| `sawLet` | 1 artifact uses it at all (prelude auto-emit); no thrower inside |
| `genM` | 0 | **dead surface — no artifact uses it** |

The 59 include the discharged proof corpus's flagship rows: all 32
`llvm_s20hash_comp` safety assertions, `cryptol_running_sum_verify`,
`llvm_popcount_verify`, `llvm_eq_u128_verify`,
`offline_lean_e_series` (E6), `offline_lean_popcount32`.

## The strategic finding

**The TODO's recorded "measured cost zero across `gen`" was true
only for user-written `error`.** The dominant in-element thrower is
`atRuntimeCheckedM` — the OP-2 evidence-less indexing route — which
throws by construction, so a syntactic "reject element bodies that
can throw" gate (option (b) as scoped 2026-07-25) rejects ~17% of
the corpus including essentially every major discharged workflow
proof. Option (b) at that scope is not a viable interim fix.

Refined option space for the decision:

- **(b-narrow)**: reject only elements that can reach
  `saw_throw_error` (user `error`) and the runtime division family.
  Measured cost: ~2 real rows (`cryptol_rev_module` — its elements
  do runtime `intDiv`/`intMod`; `fix_error_elem` — deliberate).
  Does NOT close the `atRuntimeCheckedM` half of the hazard.
- **(b-evidence)**: like (b-full) but an element is admitted when
  its only throw sources are checked operations whose obligations
  are discharged in-artifact — a discharged bounds proof makes the
  throw branch dead, the element provably `Except.ok`, and the
  collapse unobservable. Preserves the corpus; needs a design note
  arguing the dead-throw ⇒ no-collapse step and ideally a
  Lean-checked side condition rather than a translator-side claim.
- **accelerate (a)**: the faithful carrier
  (`Vec n (Except String T')`), already the agreed successor;
  0.03-scale.

Open semantic refinement, deliberately NOT resolved here: the
divergence additionally needs a downstream observer that reads only
SOME slots (the LIB-1 witness's outer `at`); whole-vector
observations force every slot on both sides. Whether that narrows
the hazard class for any of the 59 is a design-note question — a
rejection gate should not lean on it without a checked argument.

`vecSequenceM` note: SAWCore vector LITERALS are also element-lazy
in SAW (per-slot thunks), so literal elements are genuine element
positions — confirmed by the pin row, whose literal collapses.
