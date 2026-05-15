# Pre-release case-study recommendation

*2026-05-09. Companion to `2026-05-05_long-term-plan.md`. Frames a
"headline demo" for the saw-core-lean release: what would land as
genuinely impressive, what's blocked, and what capability work the
demo gates.*

## Why this doc exists

The backend is at parity with the Phase 1 surface and has three
case studies on file (A: Point, B: popcount, D: running-sum, E:
u128). Two of them (B, D, E) elaborate cleanly but stall on
discharge, exposing two recurring blockers:

- comprehension-shape Cryptol → opaque `genFix` to `bv_decide`
  (Cases B, D — `2026-05-05_case-study-d.md`),
- byte-array slicing / `foldr Bool` / `coerce` → no peeler simp
  set (Case E — `2026-05-06_case-study-e.md`).

The plan-of-record (§4.1, §4.4) already names the fixes. What's
missing is a single demo that motivates landing them on a
release-aligned timeline, rather than lazily as the next
case-study finds them.

## Brief from the user

Two prompts on the table:

1. *"Replace all SMT-backed obligations with Lean-proved
   obligations"* — i.e., for some real SAW workflow, dispatch every
   `prove` to `offline_lean` and discharge in Lean.
2. *"Replicate the Enigma example using Lean as the backend
   everywhere, no SMT remaining."*
3. *"Include a C-or-Rust → SAW → Lean mapping — that's one of
   SAW's powerful features."*
4. *"If capabilities are missing for an impressive demo, add them
   before release."*

Note that "Enigma" is from the *Cryptol* tutorial
(`deps/cryptol/docs/ProgrammingCryptol/enigma/Enigma.cry`), not
the SAW manual proper. The SAW manual's chapter-1 walkthrough is
Find-First-Set (FFS) — relevant below as the conservative
fallback.

## Reality check on the two stated ideas

### Enigma all-Lean

Enigma uses `[seed] # [body | … <- self]` self-referential
comprehensions seven times in ~150 lines (`elem`, `invSubst`,
`joinRotors`, `backSignal`, `enigma`, `all`, plus the
exercise-defined `checkPermutation`). Cases B and D already pinned
this shape's discharge path as **blocked on §4.1** (the
`genFix → Vector.foldl` bridge lemma). Enigma also uses class-
methods (`==`, `<`) on type variables, which the README flags as
unmapped (`PCmp`, `PEq` etc., currently surface as unknown
identifiers). Both blockers are on the plan but neither has
landed.

So Enigma-all-Lean is the right *scope* and exactly hits two
already-known capability gaps. Pursuing it pre-release means
landing §4.1 + class-dictionary primitives first.

### "Replace every SMT obligation"

Same shape applies: any production Cryptol that's interesting
enough to be worth a demo will hit one of:

- comprehension-shape recursion (§4.1 needed),
- memory-model byte slicing (§4.4 needed),
- polymorphic class methods (class-dictionary primitives needed),
- bitvector-gated partial recursion (currently *refused* by
  `RejectedPrimitive` — landing this is a much larger arc).

Pure-bv-arithmetic kernels (Salsa20 quarterround, ChaCha20
quarterround, ffs implementations) sidestep all four and are
discharge-feasible today via `saw_to_bitvec; bv_decide`.

## Capability surface — what's missing for an impressive demo

Roughly in priority order. None of these is new — all named in
`2026-05-05_long-term-plan.md` §4. The framing here is "which
gates does the headline demo open."

| Gap | Plan ref | Unblocks | Estimated cost |
|---|---|---|---|
| `genFix` ↔ `Vector.foldl` bridge lemma | §4.1 | every `[seed]#[…|<-self]` comprehension shape: popcount, running-sum, the round-folding step in any cipher, all of Enigma | 1–2 days; kernel-checked; no translator changes |
| `saw_simp` / `saw_decide` tactic skeleton + byte-extract / `foldr Bool` / `coerce` peelers | §4.4 | memory-model goals (Case E), reduces boilerplate across every case | ~1 day for simp set, half-day for tactic |
| Class-dictionary primitives (`PCmp`, `PEq`, `PRing`, `PIntegral`, `PArith`, `PLogic`) mapped via SpecialTreatment | README "expand as case studies demand" | every polymorphic Cryptol that uses `(==)`/`(+)` on type variables; required for Enigma but dodgeable on a monomorphic ChaCha20 demo | depends on surface; minimum-viable map for `PCmp`/`PEq`/`PRing` over fixed instances probably 1–2 days |
| `lean-smt` integration prototype (`by lean_smt` calls Z3, parses LRAT/proof certificate) | §4.2 | larger BV obligations than `bv_decide` covers; **also reframes "no SMT" as "SMT-as-kernel-checked-tactic"** which is more honest than "no SMT at all" | 1–3 days, speculative |

## The recommendation

A **paired** demo, because the user's framing splits naturally:

### Headline: ChaCha20 — C → Cryptol → Lean, kernel-checked end-to-end

- **Source**: `examples/chacha20/chacha20-crucible.saw` exists and
  currently dispatches to `abc`. The change is one line:
  swap the solver for `offline_lean`. C bitcode is already
  shipped; the Cryptol spec is in
  `deps/cryptol-specs/Primitive/Symmetric/Cipher/Stream/chacha20.cry`.
- **Why this**: production cipher (TLS, OpenSSH, WireGuard).
  "Real C, every byte checked by Lean's kernel" is a defensible
  pitch.
- **Cryptol shape**: per-round operations are pure rotate-add-xor
  (the same class as Case A and predicted Case C). State mixing
  is indexing-heavy, sidestepping much of the comprehension
  blocker if the demo is scoped to per-round equivalence first
  and full-stream second.
- **Discharge plan**: per-round closes via `saw_to_bitvec;
  bv_decide`. Round-folding closes via `rw
  [genFix_acc_eq_foldl]; bv_decide` — the §4.1 bridge applied
  once. Composition is structural induction. No SMT solver
  invoked outside the LRAT-checked SAT call inside `bv_decide`.
- **Gates needed**: §4.1 (round-folding), §4.4 (light — the LLVM
  side has byte-array reasoning that benefits from peelers).
  Class-dictionary primitives can be dodged by monomorphizing
  the Cryptol spec.

#### Status update (2026-05-09 evening)

**Per-round equivalence: LANDED.**
`otherTests/saw-core-lean/drivers/llvm_chacha20_q_verify/` couples the
unmodified reference C `qround` to the unmodified reference Cryptol
`qround`; SAW's `offline_lean` closer emits the state-equality goal;
`otherTests/saw-core-lean/proofs/llvm_chacha20_q_eq/proof.lean`
discharges it with `bv_decide` (LRAT-checked SAT). End-to-end: C source
→ Cryptol spec → Lean kernel-checked proof.

**§4.1 bridge library: LANDED, kernel-checked.**
Three parametric theorems in `SAWCorePrelude_proofs.lean` with axioms
`{propext, Classical.choice, Quot.sound}`:
- `saw_self_ref_comp_iterate` — bridges SAW's outer `atWithDefault/gen/
  genFix/zip` chain (Phase 5 Slice B-shape) to `Nat.rec`.
- `foldl_eq_natRec_atWithDefault` — bridges Vector.foldl to Nat.rec.
- `mkStreamFixIdx_eq_genFixIdx` — bridges Phase 5 Slice A `iterate`
  emissions to the `genFix` form so the same bridge fires.
- `foldr_and_gen_eq_true_of_all` — peels foldr-AND-of-gen elementwise-
  equality goals (used by ChaCha20 quarterround discharge).

**Width-32 popcount via the bridge: LANDED** (pre-flight stress test).

**Round-folding (`core` function over 10 doublerounds): LANDED.**
The polymorphic-iterate translator extension (commit `a4d92631a`)
recognizes Cryptol's `iterate : { a } (a -> a) -> a -> [inf]a` as a
3-Pi/4-lambda/MkStream `Prelude.fix` shape and lowers it to
`CryptolToLean.SAWCorePreludeExtra.cryptolIterate` — a structurally-
recursive Lean def. `chacha20::core x` translates to 322 lines of
Lean (was: "Refusing to translate primitive fix") with a literal
`cryptolIterate (Vec 16 (Vec 32 Bool)) cdround x` in the body.

`otherTests/saw-core-lean/drivers/cryptol_chacha20_core_iterate/`
pins the emission; the discharge in
`otherTests/saw-core-lean/proofs/cryptol_chacha20_core_iterate/proof.lean`
closes `core x == core x` via `foldr_and_gen_eq_true_of_all 64` +
`bvEq_refl` over 64 output bytes — 4 tactic lines, no `sorry`. End-
to-end: unmodified Cryptol spec → polymorphic-iterate-aware
translation → Lean kernel-checked proof.

**C↔Cryptol coupling status (commit pending).**
`otherTests/saw-core-lean/drivers/llvm_chacha20_core_verify/` couples
the unmodified reference C `qround` to the unmodified reference
Cryptol `qround` at each of the 8 fixed `(a, b, c, d)` index tuples
that `core` invokes per doubleround. The 8 SAW verifications cover
all 80 quarterround invocations in one ChaCha20 block, and each
emits a ~200-line Lean goal that elaborates cleanly.

Two open pieces remain:

1. **Compositional `core` verification.** Passing the 8 `LLVMSpec`s
   as overrides to `llvm_verify "core"` unblocks SAW's per-qround
   symbolic execution, but the resulting `core` post-state has 80
   nested Cryptol `update`s wrapping `qround` calls that SAW's
   normalizer cannot canonicalise tractably (>10 min). Two paths:
   per-doubleround override helpers, or a SAW-side normalizer
   improvement that handles the `update`-chain shape efficiently.

2. **Per-tuple Lean discharge.** The 8 emissions follow the
   `llvm_chacha20_q_eq` template structurally, but the override-
   driven emission has `bvToNat (bvNat n)` wrappings on state
   indices (because the spec's `update state idx ...` retains the
   `[32]` index width) that push the existing bare-`simp` past 10M
   heartbeats. The fix is a more focused simp set (or surgical
   unfolds replacing `simp`) — mechanical follow-up work not
   blocked on any translator or library change.

### Charm: Enigma — Cryptol → Lean, all-Lean, post-class-dictionary

- **Source**:
  `deps/cryptol/docs/ProgrammingCryptol/enigma/Enigma.cry`. No C
  side; the demo is "the Cryptol tutorial's Enigma, but every
  property dispatched to and proved in Lean."
- **Why this**: SAW community recognition. "We redid the Cryptol
  tutorial in Lean" is a clean blog post. Properties to verify:
  `dEnigma ∘ enigma = id` (involution), `checkReflectorFwdBwd`,
  `checkPermutation`.
- **Gates needed**: §4.1 (every comprehension), class-dictionary
  primitives (Enigma uses `(==)` polymorphically on `Char` and
  on rotor tuples), §4.4 (light).
- **Position**: lands *after* the headline. Reuses every gate
  the headline opens.

### Conservative fallback if §4.1 slips

**Find-First-Set multi-implementation equivalence**, mirroring
`doc/llvm-java-verification-with-saw/example-find-first-set.md`.
Four C implementations of `ffs` (reference loop, byte-skipping,
musl-libc trick, deliberately-buggy), all dispatched to Lean.
Pure bv arithmetic, no comprehensions, **fits today's
capabilities with zero new infrastructure**. The buggy
implementation lets the demo show counterexample extraction from
`bv_decide`'s LRAT certificate — i.e., Lean is doing the same
two jobs the SAW manual chapter shows ABC doing. Less impressive
cryptographically than ChaCha20, but it is the literal answer to
"replicate an existing SAW manual case study with Lean as the
backend everywhere."

## What this means for the long-term plan

§4.1 was already next per the case-study ladder
(`2026-05-05_long-term-plan.md` §4). What changes if this doc is
adopted:

- §4.1 and §4.4 become release-blockers rather than
  "case-study-driven, when convenient."
- Class-dictionary primitives move from "expand as case studies
  demand" to "minimum-viable map for the fixed instances ChaCha20
  uses, with Enigma demand pinning the broader surface."
- §4.2 (`lean-smt`) becomes attractive earlier — letting the
  pitch be "every proof is kernel-checked, including the parts
  that go through SMT," which is a cleaner story than "no SMT
  anywhere" once the user notices `bv_decide` already calls
  CaDiCaL.
- The ChaCha20 driver under `otherTests/saw-core-lean/drivers/`
  gets pinned as a `.log.good` / `.lean.good` regression target
  before the discharge lands; same pattern Cases D and E used.

## Decision points

1. **Do we adopt this paired demo as the release headline?** If
   yes, §4.1 and §4.4 land before further case-study additions
   on the ladder.
2. **ChaCha20 vs. Salsa20 for the headline.** Salsa20 is already
   Case C on the ladder (predicted half-day), and is the
   simpler kernel. ChaCha20 has stronger production recognition.
   I'd argue Salsa20 quarterround as a *stepping-stone* discharge
   that proves out the per-round pattern, then ChaCha20 as the
   full-stream demo.
3. **Class-dictionary primitives surface.** Minimum-viable
   (one or two instances at fixed types) vs. the broader
   `PCmp`/`PEq`/`PRing` surface needed for arbitrary polymorphic
   Cryptol. The first lets ChaCha20 land; the second lets Enigma
   land. Stage in that order.
4. **`lean-smt` track timing.** Defer to post-headline, OR pull
   forward if the headline pitch is reframed around
   "kernel-checked SMT" rather than "no SMT."
