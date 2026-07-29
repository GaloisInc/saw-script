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
| `genWithBoundsM` | 59 | 58 × `atRuntimeCheckedM`; 1 × `saw_throw_error` (the LIB-1 pin row itself); `cryptol_rev_module` additionally `intDiv_runtimeM`/`intMod_runtimeM` |
| `vecSequenceM` | 2 | the LIB-1 pin row; `bitvector_order_width` (`atRuntimeCheckedM` in a literal element) |
| `foldrM` | 0 | used in 28 artifacts, never with a thrower inside the folded function |
| `foldlM` | 0 | used in 6 artifacts, same |
| `sawLet` | 0 | **UNMEASURED, not clean — see below** |
| `genM` | 0 | **dead surface — no artifact uses it** |

**CORRECTIONS 2026-07-29 (session audit).** Three errors in the
table as first published, none of which move the headline 59:

- The `atRuntimeCheckedM` count was **58, not 57** — as first
  published the sub-breakdown did not sum to its own headline
  (57 + 1 = 58 ≠ 59). Recount: 58 artifacts with `atRuntimeCheckedM`
  in a `genWithBoundsM` element position, plus the 1 with
  `saw_throw_error`, = 59.
- `fix_error_elem` was listed in the thrower breakdown as an "error
  deliberately REACHED" entry. It contains **no `saw_throw_error`
  at all**; its in-element thrower is `atRuntimeCheckedM`, so it is
  an ordinary member of the 58 and the parenthetical was wrong.
- `sawLet` is **unmeasured, not measured-clean.** Its single corpus
  "hit" is a COMMENT line recording that `sawLet` was skipped
  (`drivers/sawcore_prelude_auto_emit/…prelude.lean`), not a use.
  The surface has zero emitted uses, so the corpus says nothing
  about it either way — and `sawLet` is a DISTINCT instance of the
  hazard, not a variant (SAW beta-reduces and DISCARDS a throwing
  bound value when the body ignores it; the Lean realization
  propagates it). It stays an open question for the (a) carrier
  work, and the shipped user-facing framing (README,
  residual-trust §3.2e) describes the vector carrier only.

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
  Measured cost: exactly 2 artifacts — `cryptol_rev_module`
  (elements do runtime `intDiv`/`intMod`) and the LIB-1 pin row
  itself, i.e. ONE real row plus the pin. (Corrected 2026-07-29,
  session audit: the first version named `fix_error_elem` as the
  second hit, but its only in-element thrower is
  `atRuntimeCheckedM`, which (b-narrow) explicitly does not reject —
  the count of 2 was right over the wrong membership.)
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

## The census is now checked in (2026-07-29)

The numbers above were produced by a one-off scratch script. A user
bounds their exposure to LIB-1 by them, so they are now RE-DERIVED on
every full run rather than re-asserted:
`otherTests/saw-core-lean/support/lib1-census.py`, invoked by
`test.sh` after every emission category. It asserts three facts and
fails loudly on any change: in-element throwers = 59, reference-closure
escapes = 0, and the corpus SIZE.

The size assertion is not bookkeeping. The harness deletes and
re-emits artifacts as it runs, so a census over a partial corpus
reports a LOWER count — understating exposure, silently. That was
found by making the mistake: scanning mid-sweep reported 27/324 and
read as good news.

**A blind spot the pin exposed, recorded rather than quietly patched.**
The element scan recognises an element position spelled as a lambda
(`(fun … )`), which is how the emitter writes `gen`/`fold` element
functions — but not a bare partially-applied name in the same slot,
which the under-applied partial-op path emits
(`foldlM … (bvUDiv_runtimeM 16) …`, from the row added the same day).
That shape is not a LIB-1 hazard for an independent reason — a left
fold forces every element on both sides, so there is no unforced-slot
divergence — which is why the published count is unaffected. But the
two facts are independent, and a collapsing helper that is lazy in a
bare-name element argument would be missed. Widening the scan would
move the published number for a reason unrelated to the hazard; the
honest fix is the (a) carrier, which removes the class.
