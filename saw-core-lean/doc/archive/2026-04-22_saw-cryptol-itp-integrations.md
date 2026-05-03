# SAW / Cryptol → ITP integrations: current landscape

*Research note — 2026-04-22*

Background for the claude-lean-saw project: a survey of what already exists for
connecting the SAW / Cryptol ecosystem to interactive theorem provers (ITPs),
so we know what to reuse, what to skip, and where the gap for Lean actually
sits.

## The main, actively-maintained integration: SAWCore → Coq/Rocq

The primary bridge is **`saw-core-coq`** (recently renamed `saw-core-rocq`
following the Coq → Rocq rebrand). It lives inside the `GaloisInc/saw-script`
monorepo; the standalone `GaloisInc/saw-core-coq` repo was archived in April
2021 after the code was absorbed upstream.

What it does:

- Translates SAWCore (SAW's dependently-typed internal language, deliberately
  Coq/Lean-shaped) to Gallina.
- Ships both auto-generated support libraries (regenerated from the
  SAWCore/Cryptol preludes) and hand-written Coq extensions.
- Exposes SAW-script commands for exporting terms and proof goals:
  - `write_rocq_term` (was `write_coq_term`)
  - `write_rocq_cryptol_module` (was `write_coq_cryptol_module`)
  - `write_rocq_sawcore_prelude` (was `write_coq_sawcore_prelude`)
  - `offline_rocq` tactic (was `offline_coq`) — punts the current proof goal
    to an external Rocq file
- In SAW 1.5 (mid-2025) the old `coq`-prefixed names were deprecated but kept
  as aliases.

## Cryptol → Coq: `cryptol-semantics`

`GaloisInc/cryptol-semantics` is a Coq formalization of Cryptol's denotational
semantics. Stated goals: give confidence that Cryptol programs mean what they
look like, verify SAW itself, and anchor trust for verified compilation.
Includes case studies on OTP, HMAC (vs. the FCF spec), and a partial SHA-256
equivalence. Status is dormant — the repo still pins Coq 8.6 and has seen
essentially no activity for years.

## Heapster (C → Coq via interaction trees) — recently removed

Heapster was a permission/separation type system built on top of SAW that
extracted functional specifications of memory-safe C programs to Coq,
expressed in a SpecM/ITree monad (the `heapster-formalization` and
`heapster-saw` repos). **It was removed entirely in SAW 1.5.** So if you're
looking at post-2025 SAW, this pipeline is gone — though the research
artifacts (OOPSLA '21 paper, ECOOP '23 paper on ITree specifications) remain
relevant prior art.

## Isabelle/HOL

Historical: early Cryptol had a "manual mode" that emitted Isabelle/HOL
specifications, and there is related work in the broader Isabelle ecosystem
(CryptHOL for cryptographic arguments). This is not an actively maintained
pipeline today.

## SMT-LIB / What4 / Verilog / AIGER — "offline" exports (not ITP, but adjacent)

SAW and Cryptol can write goals to SMT-LIB 2 (`write_smtlib2`,
`w4_offline_smtlib2`), Verilog (`write_verilog`, `offline_verilog`), AIGER,
DIMACS, and shared SAWCore. These are the paths automated solvers consume —
not interactive proof — but they're the main "export" surface for external-
tool handoff.

## Lean

There is **no official SAW or Cryptol → Lean integration**. Earlier
SAW/VSTTE-era material mentioned Lean as a possible future target alongside
Coq (SAWCore was designed to be translatable to either), but nothing has
shipped. The closest things in the Lean ecosystem are independent:

- Lean 4 cryptography work like *Computationally-Sound Symbolic Cryptography
  in Lean* (eprint 2025/1700).
- General Rust → Lean pipelines (Hax, which targets F*, Rocq, and Lean) —
  relevant as prior art for "verified-DSL → Lean" translation but not
  Cryptol-specific.

This gap is exactly the opening for the project.

## Summary table

| Target ITP | Project | Status |
|---|---|---|
| Coq/Rocq | `saw-core-coq` / `saw-core-rocq` (in `saw-script`) | **Active**, renamed to Rocq in SAW 1.5 |
| Coq | `cryptol-semantics` | Dormant (~Coq 8.6) |
| Coq | Heapster (C → Coq via ITrees) | **Removed in SAW 1.5** |
| Isabelle/HOL | Legacy Cryptol manual-mode output | Historical |
| Lean | — | **None** |
| SMT-LIB / Verilog / AIGER | `write_smtlib2`, `write_verilog`, etc. | Active (automated, not ITP) |

## Implications for a Lean bridge

Two plausible entry points, with different tradeoffs:

1. **SAWCore → Lean 4.** Shortest path to a "real" ITP integration — SAWCore
   is dependently-typed and close to Lean's kernel, and `saw-core-rocq` is an
   existing blueprint. You'd mirror its architecture: a term translator plus
   a Lean port of the SAWCore/Cryptol prelude support libraries. Expose
   `write_lean_term` / `offline_lean` alongside the Rocq commands.
2. **Cryptol → Lean directly** (analogous to `cryptol-semantics` but in
   Lean 4 + mathlib). More foundational, more work, and overlaps with the
   dormant Coq effort.

## Sources

- [GaloisInc/saw-core-coq (archived)](https://github.com/GaloisInc/saw-core-coq)
- [GaloisInc/saw-script](https://github.com/GaloisInc/saw-script)
- [SAW changelog (Rocq rename, Heapster removal)](https://github.com/GaloisInc/saw-script/blob/master/CHANGES.md)
- [GaloisInc/cryptol-semantics](https://github.com/GaloisInc/cryptol-semantics)
- [GaloisInc/heapster-saw](https://github.com/GaloisInc/heapster-saw)
- [Galois — SAW 1.5 / Cryptol 3.5 release notes](https://www.galois.com/articles/galois-releases-saw-1-5-and-cryptol-3-5-0)
- [Galois — SAW 1.3 / Cryptol 3.3 release (April 2025)](https://www.galois.com/articles/galois-releases-new-versions-of-verification-tools-saw-cryptol-and-crux-april-2025)
- [SAW VSTTE paper (SAWCore as Coq/Lean-shaped)](https://saw.galois.com/files/saw-vstte-final.pdf)
- [He et al., *A Type System for Extracting Functional Specifications* (OOPSLA '21)](https://www.cis.upenn.edu/~stevez/papers/HW+21.pdf)
- [Interaction Tree Specifications (ECOOP '23)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol263-ecoop2023/LIPIcs.ECOOP.2023.30/LIPIcs.ECOOP.2023.30.pdf)
- [Computationally-Sound Symbolic Cryptography in Lean](https://eprint.iacr.org/2025/1700)
