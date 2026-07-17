# saw-core-lean — Long-term plan (case-study-driven)

*Written 2026-05-05, supersedes the per-Phase plans in `doc/archive/2026-05-02_revised-plan.md` and `doc/archive/2026-05-02_post-audit-plan.md` for prioritization purposes (those remain accurate as historical accounts of work shipped).*

## 1. Where we are

**Infrastructure: solid.**
- Soundness lockdown L-1..L-17 with the exposure-surface inventory and hostile-prover audit (`doc/2026-05-04_exposure-surface.md`).
- Test infrastructure consolidated (Phase F): everything Lean-backend-specific lives under `otherTests/saw-core-lean/`, organized as `drivers/ proofs/ shape/ saw-boundary/`. Single CI gate: `make test-saw-core-lean`.
- Translator at parity with Phase 1 plus several finds-and-fixes from case studies: free-var abstraction in `writeLeanProp`, `escapeIdent` for local vars, `error_unrestricted` consistency in `genFix` slots, constant-fold pass on Nat/Int/Bool literals (Improvement #1, ~38% emission size reduction).

**Case-study evidence: thin.** Only two real case studies (workflow = LLVM verify against Cryptol spec, dispatched to Lean via `offline_lean`):

| Study | Outcome | What we learned |
|---|---|---|
| **A. Point.cry** (struct equality) | Discharged in 6 tactic lines, [propext]-only soundness | Pure bvAdd/bvAnd-style equivalences are easy. The translator + tactic library handle this class cleanly. |
| **B. Popcount** (Hacker's Delight ↔ Cryptol comprehension) | C-side reaches `bittwiddle32 = naive32` (solved by `bv_decide` in <2s). Cryptol-side blocked at `genFix` bridge | Comprehension-shape Cryptol (`[seed] # […|<-self]`) emits a tactically-opaque genFix recursion. **This is the dominant pain point for any non-trivial Cryptol case.** |

Two data points isn't enough to tell us:
- Whether the genFix issue is the dominant pattern or a single class.
- Whether other pain points exist beyond comprehension reasoning (loops, memory model, arithmetic-on-Nat, table lookups, …).
- What "moderate-sized" case studies actually look like for end users.

**Conclusion: more empirical evidence is the highest-leverage next move.** Translator and tactic-library investments are real but speculative without case-study signal pointing at them.

## 2. Strategic principles

### 2.1 Hybrid Lean + SMT, not Lean-or-SMT

The goal is **not** to discharge every SAW obligation in Lean. The right end-state is:

- Lean handles structural / inductive / dependently-typed reasoning where SMT can't go.
- SMT (Z3 / Yices) handles SAT-style BV equivalences efficiently.
- Mixed proofs: Lean structures the proof; calls out to SMT for sub-goals where the heavy lifting is bit-vector decision procedures.

Concretely: `bv_decide` in Lean is already this hybrid (it uses CaDiCaL with LRAT-checked output). For richer queries — e.g., "this Cryptol fold equals this BV expression for all inputs" — we want a Lean tactic that translates the Lean goal to SMT-LIB, calls Z3, parses back a proof certificate. That's the **lean-smt experimentation track** below.

### 2.2 Case-study-driven, with hypotheses

Each new case study tests a specific hypothesis about what's hard. We rank them by what they'd reveal, not by what we want to prove. After every 2-3 cases, re-plan.

### 2.3 Pruning is part of progress

The synthetic stress tests (E1-E7) were a translator-finding exercise. They served their purpose. They're now inertia. Once a case study is in place, retire the synthetic tests it subsumes. Same for tasks filed before we had case-study evidence.

### 2.4 Obvious-correctness in the translator (load-bearing)

**The translator should be obviously correct by inspection.** Every additional semantic transformation it performs is an additional soundness surface — a place where translator output could diverge from SAW semantics in a way our test fixtures don't catch. We strongly prefer:

- **Translator: near-syntactic rewrite.** SAWCore term → Lean AST with one-to-one structural mapping. SpecialTreatment dispatches names; binders, applications, and recursors translate in-shape. Literals, primitive references, and recursion shapes are emitted faithfully — not "improved."
- **Lean library: where equivalences live.** Anything of the form "this SAW shape is equivalent to that simpler/faster Lean shape" should be a *theorem* in the Lean support library, with a proof, applied by the user (or by a saw-tactic) at proof time. Soundness then reduces to: "did the lemma's proof go through?" rather than "is the translator's pattern-matcher really capturing all and only the cases where this rewrite is valid?"

Concretely this affects three classes of work:

1. **Existing translator transformations** stay only if they're trivially safe by inspection. The constant-fold pass on closed Nat/Int/Bool literals (Improvement #1) qualifies — it's literal arithmetic on closed terms with no shape-pattern, and a literal mismatch would be caught by the .good fixtures. The Phase 5 BoundedVecFold → genFix lowering is on the edge: the recognizer is a shape pattern, and even though the resulting `genFix` is itself a faithful definitional unrolling, future enhancements down that path (e.g., emitting `Vector.foldl` directly) cross the line.

2. **Future shape-recognizer translator work is presumptively rejected.** The default answer for "should the translator detect pattern X and emit shape Y?" is *no*. The right move is to emit X faithfully and prove `X = Y` once in the Lean library.

3. **Discharge tactics carry the burden of cleverness.** A `saw_simp` set, a `saw_decide` tactic, a Lean-side bridge lemma — these are where pattern-matching and rewrites belong. They're checked by Lean's kernel. The translator stays dumb; the proof library is allowed to be smart.

The invariant we're protecting: a reader auditing the translator should be able to say "yes, this is `Eq → CryptolToLean.Eq`, this is `genFix → genFix`, no surprises" without needing to verify a semantic claim. The smarts go where Lean can check them.

## 3. The case-study ladder

Ordered roughly by what each new case would teach. Not all of these need to land — if cases C/D both confirm the genFix-foldl hypothesis, we may pivot to translator work instead of doing E.

### C. Salsa20 quarterround (next)
- **Source**: `exercises/functional-correctness/salsa20/`. Existing SAW solution proves LLVM matches Cryptol.
- **Cryptol shape**: bv rotation + XOR, NO comprehension recursion. Pure arithmetic.
- **Hypothesis tested**: pure-bv-arith case studies are easy by `bv_decide`, even at non-trivial size.
- **Predicted outcome**: discharges cleanly in ~10 lines like Case A. If it doesn't — that's a new pain point worth investigating.
- **Effort**: ~half-day.

### D. fib-like sequence at small width
- **Source**: synthetic but very real shape — `[0, 1] # [a + b | a <- fibs | b <- drop`1` fibs]` style.
- **Cryptol shape**: self-referential comprehension with two prior values. Same `[seed] # […|<-self]` pattern as popcount.
- **Hypothesis tested**: is the popcount stall genuinely about the genFix shape, or specific to popcount's particular body? If fib stalls similarly, the fix is shape-level — and per §2.4 the right response is a **Lean-side bridge lemma** (`genFix_unrolled_eq_foldl` or similar) plus a `saw_decide`-style tactic that applies it, NOT a translator-side rewrite.
- **Predicted outcome**: same blocker as Case B, motivates investing in the Lean-side bridge library (§4.1 below).
- **Effort**: ~half-day.

### E. u128 byte-by-byte equality
- **Source**: `exercises/functional-correctness/u128/`. Existing SAW solution.
- **Cryptol shape**: simple equality but goes through LLVM memory loads/stores.
- **Hypothesis tested**: do `llvm_verify`-emitted memory-model artifacts (load/store, alloc, struct projection) translate cleanly? Case A had simple structs; this stresses byte-array reasoning.
- **Predicted outcome**: minimum viable. If it stalls, we have a memory-model translator pain point to address.
- **Effort**: ~half-day.

### F. Verified swap function (in-place array mutation)
- **Source**: `exercises/functional-correctness/swap/`.
- **Cryptol shape**: array permutation property. C side has imperative mutation.
- **Hypothesis tested**: does mutation reasoning lift through `llvm_verify` to a Lean-tractable goal? This is a real product-shape question for SAW.
- **Predicted outcome**: probably hits new pain points around array-update reasoning.
- **Effort**: 1 day.

### G. AES S-box equivalence
- **Source**: known SAW exercise (table lookup vs. mathematical computation). May need to source the implementation.
- **Cryptol shape**: pure bv arithmetic, but stresses the SAT solver (S-box has 256 cases).
- **Hypothesis tested**: where's `bv_decide`'s ceiling? Is it solver-time or solver-correctness that becomes the bottleneck on larger BV obligations?
- **Predicted outcome**: works but slow, OR exposes solver heuristic gaps. Either way, motivates the lean-smt experiment track.
- **Effort**: ~half-day to a day.

### H. SHA-256 single round
- **Source**: synthetic — extract one round of SHA-256 from the Cryptol spec. Don't try the full algorithm.
- **Cryptol shape**: bv rotation + addition + and/or/xor, nested.
- **Hypothesis tested**: do moderately-deep bv expressions discharge through `bv_decide` at scale, or do they need structural decomposition?
- **Predicted outcome**: closes by `bv_decide` if the round is small enough; an ordering effect on `simp` arguments may matter.
- **Effort**: ~1 day.

### Stop conditions

After cases C+D (just two): we know whether the genFix issue is the dominant comprehension blocker. If yes, pivot to **§4.1 Lean-side bridge library** (NOT translator-side foldl emission — see §2.4) before continuing the ladder.

After cases C+E (or D+E): we know whether memory-model is a separate pain point. If yes, that becomes its own track — and again, default to Lean-side bridge lemmas over translator-side rewrites.

After 4-5 cases: we have a saturated empirical picture. Plan for 2026-05-15 to re-plan.

## 4. Translator / tactic-library / proof-library work, gated by evidence

Re-prioritized under the obvious-correctness principle (§2.4): Lean-side proof infrastructure leads, translator-side work is presumptively a last resort.

### 4.1 Lean-side bridge library for genFix shapes *(highest impact, soundness-aligned)*
- **Triggered by**: Case B blocker; needs Case D to confirm the shape generalizes.
- **What**: prove general lemmas in `CryptolToLean.SAWCorePreludeProofs` of the form `genFix … = Vector.foldl … seed (range n)` for the accumulator-comprehension shape, plus per-element-type instances when needed. User code closes popcount-style goals with `rw [genFix_acc_eq_foldl]; bv_decide` or via a `saw_decide` tactic that applies the bridge automatically.
- **Why this over translator-side rewriting**: the equivalence is checked by Lean's kernel, not by translator pattern-matching. A bug in our recognizer would break a proof, not silently mistranslate. (§2.4)
- **Cost**: 1-2 days for the core lemma + a half-day for tactic glue. No `.good` churn — translator output unchanged.
- **Unlocks**: popcount, fib, salsa20-comprehension shapes, anything that fits the accumulator pattern.
- **Risk**: the lemma may need to be parametric over the body — proving the general form is harder than proving a per-instance bridge. Mitigation: start with the per-instance version (§4.3) as a stepping stone and generalize once the proof shape is clear.

### 4.2 Lean-SMT experimentation track *(speculative, high upside)*
- **What**: integrate `lean-smt` (UFMG project that translates Lean goals to SMT-LIB and back with checked proofs) so user discharges can do `by smt` for BV-heavy sub-goals.
- **Why**: `bv_decide` covers SAT-style BV equivalences but bottlenecks on bigger queries. SMT solvers (Z3 in particular) handle larger BV problems and richer theories. A Lean tactic that calls Z3 with a checked-proof return path is the natural extension of the hybrid Lean+SMT principle (§2.1) and aligns with §2.4 — the "smart" component lives in the discharge tactic, where soundness is ensured by checking Z3's certificate, not in the translator.
- **Approach**: prototype on Case G (AES S-box) where `bv_decide` is expected to bottleneck. If `lean-smt` discharges it, that's a new tool in the box for harder cases.
- **Cost**: 1-3 days for the prototype, depending on `lean-smt` API maturity and how much wiring is needed.
- **Risk**: `lean-smt` may not yet handle the specific BV fragment SAW emits; experimental.

### 4.3 Bridge lemma for Case B *(stepping stone for §4.1)*
- **Task #141.** Write `cryptol_genFix_popcount32 = naive32` as a structural induction over genFix's 32 unrolls. ~half-day.
- **Now positioned as**: the concrete proof from which §4.1's general lemma is generalized. Doing the per-instance proof first is the right way to discover the general statement — the unfolding pattern for one shape teaches us what the general statement should look like.

### 4.4 saw_simp + saw_decide tactic helpers *(library-level, soundness-aligned)*
- **Task #131.** A `saw_simp` simp set (collect all the SAW reducible aliases + reduction lemmas) and a starter `saw_decide` tactic that applies the §4.1 bridge lemmas plus `bv_decide`. Reduces boilerplate in proof.lean files and is the natural home for §4.1's bridge lemmas to be applied.
- **Effort**: ~half-day for the simp set; another half-day for the tactic skeleton once §4.1 lands.
- **Evidence supporting**: each new case study currently re-discovers the same simp set. Real friction.

### 4.5 *(deprecated)* Phase 5 BoundedVecFold → Vector.foldl emission
- **Previously the lead candidate.** Demoted under §2.4: emitting a different shape than what SAW produced is exactly the kind of translator-side cleverness the obvious-correctness principle rules out. The semantic claim "this `fix … gen` accumulator = a `Vector.foldl`" belongs in the Lean library as a theorem (§4.1), not in the translator's pattern-matcher.
- **Kept on file** only as a "break glass" option if §4.1 fails AND `lean-smt` (§4.2) fails AND we need to ship something for end users. We would need explicit user sign-off before going down this path.

### 4.6 CSE / let-sharing on emission *(deprioritize for now)*
- **Task #132.** Improvement #1 already addressed most of the size pressure. Hold unless a case study surfaces a clear duplicated-subterm pain point. Note: per §2.4, even a CSE pass needs scrutiny — it's a translator-side rewrite. Acceptable only if the equivalence (`let x = e in body x` = `body e`) is structural and not shape-pattern-matching.

### 4.7 Library lemmas in emission shape *(low priority)*
- **Task #130.** Audit existing lemmas, restate in `subNat`-shape rather than `Nat.sub`-shape. Currently working via reducibility unification (E5 case shows). Keep open but defer until something actually bites. *Aligned with §2.4* — this is exactly Lean-side work to bridge between SAW emission shape and Lean-natural form.

### 4.8 Audit existing translator transformations against §2.4
- **New task** (file separately). Walk through `Exporter.hs` and `Term.hs` and tag each rewrite/normalization with: trivially-safe (constant-fold, alpha-renaming) vs. shape-recognizing (BoundedVecFold lowering) vs. semantic (any unfold/reduction step). For shape-recognizing or semantic transformations, decide: keep with stronger justification, replace with Lean-side equivalent, or remove. Estimated half-day; should produce a written justification per transformation that survives.

## 5. The lean-smt experiment in more detail

The user's note: *"experiment with Lean-SMT, which would allow us to more cleanly replicate some of SAW's symbolic reasoning but in Lean."*

This is the right framing. What SAW does is: lower a SAWCore term to an SMT query (via `what4`/SBV), call the solver, get UNSAT and trust the result. The dispatched-to-Lean variant should mirror this:

- User has a Lean goal that's BV-decidable.
- `by lean_smt` (or whatever the tactic is named) translates the Lean goal to SMT-LIB.
- Z3 (or another solver) runs.
- Z3 returns UNSAT + a proof certificate (DRAT/LRAT or full Z3 proof).
- Lean checks the certificate.

Compared to `bv_decide`:
- `bv_decide` bit-blasts to SAT, runs CaDiCaL, checks LRAT. Specific to BV.
- `lean_smt` would handle richer SMT theories (uninterpreted functions, arrays, quantifiers within decidable fragments).

Concrete experiment: take a SAW goal that `bv_decide` can't close (e.g., one involving Cryptol's `Eq` typeclass dispatch over `Stream`-like types with unfair quantification), and see if `lean_smt` reaches it.

If this works, it's a third tactic in the discharge toolbox alongside `bv_decide` and structural induction.

## 6. Pruning list

Tasks that look stale or subsumed:
- **#122 (E8 Nat-induction)** — synthetic; subsumed by case studies. Delete.
- **#123 (E9 mathlib BitVec bridge)** — subsumed by Case A (Point) which already validates the bridge. Delete.
- **#124 (E10 full popcount vs mathlib)** — subsumed by Case B (Popcount). Delete.
- **#126 (E6 inductive)** — subsumed by #141 / Phase 5 foldl emission. Delete.
- **#138 (test consolidation prune)** — execute now. Removes E1-E7 stress tests, prunes redundant primitive driver tests.
- **(any task tagged "Path 2" / "BoundedVecFold → Vector.foldl emission")** — demote per §2.4 / §4.5. Don't delete the entry yet, but mark as deprecated and pointed at §4.1.
- **#68 (Phase 7 proof-side tooling)** — too broad as-is. Re-scope as #131 (saw_simp/saw_decide) plus future per-case-study lemmas.
- **#78 (Phase 6 Cryptol surface expansion)** — keep but re-scope: only expand surface as case studies demand specific primitives.

Tasks that stay relevant:
- **#114 (Phase 9 Native Lean.BitVec)** — in progress, useful for tactic ergonomics.
- **#134 (CI gap stale .good detection)** — open, infrastructure win.
- **#141 (popcount bridge)** — fallback if 4.1 doesn't land.
- **#130, #131, #132 (Improvements #4, #5, #6)** — re-scope per §4 above.

New tasks to file:
- Case Study C (Salsa20).
- Case Study D (fib-like).
- (and so on, lazily, one at a time).
- §4.1 Lean-side genFix bridge library.
- §4.8 Audit existing translator transformations against §2.4.
- Lean-SMT integration prototype.

## 7. Cadence

- One case study at a time.
- After each: short writeup (`doc/<date>_case-study-<letter>.md`) — what worked, what didn't, what new pain point if any.
- Every 2-3 cases: re-evaluate the ladder. Some cases will be redundant; new ones may emerge.
- Translator / tactic-library work: only when 2+ case studies converge on a pain point.
- Re-plan checkpoint: 2026-05-15 (one week from now) — review case-study findings, re-rank ladder.

## 8. Decision points right now

Four things need a directive answer:

1. **Do we execute the prune list (§6) now or after the next case study?** I'd vote NOW — the synthetic stress tests are noise that confuses signal in any future debugging.

2. **Which case study next?** Default = C (Salsa20). It's a hypothesis test about pure-bv-arith case studies.

3. **Do we start the lean-smt experiment in parallel?** I'd say wait for Case G (AES S-box) where it's likely to be needed; doing it pre-emptively risks building infrastructure for a problem we haven't seen yet.

4. **Scope of §2.4 obvious-correctness audit (§4.8)** — should this run now (before Case C) or after the next 1-2 case studies? Arguments for now: clarifies the soundness story before adding more translator work. Arguments for later: case studies may surface their own findings about which existing transformations matter. I'd vote for **now, lightly** — produce the inventory, but only act on the most-suspect transformations; defer the rest pending case-study evidence.
