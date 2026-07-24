# Second pre-release soundness audit — saw-core-lean

**Date:** 2026-07-24 (same day as, and independent of,
`2026-07-24_soundness-audit.md`). **Status:** COMPLETE — all six lanes
reported and folded in.

## Recommended action order

1. **A-1 + A-6** — extend `proof-source-lint.awk:168` with
   `notation|syntax|infix|infixl|infixr|prefix|postfix|declare_syntax_cat|binder_predicate|unif_hint|export`,
   and add `gsub(/[«»]/, "", out)` before the match. Zero of the 119
   proof-side files break. **Note the lint is the fix for A-1 — a
   probe rename does not work** (verified).
2. **A-5** — replace the `#check` binding probe with a kernel-checked
   declaration and audit *it*:
   `theorem __replay_binding : goal := goal_closed` +
   `#print axioms __replay_binding`. Verified to catch both A-5 and
   A-1. Apply A-7 in the same pass.
3. **S-1** — make the fix/stream obligations defeq-visible (route
   through `Classical.choose` as `saw_mkStream_choose` already does),
   and/or add the authority-obligation-line presence gate. **Run the
   two S-1 witnesses through the real `lean-check-core.sh` first** —
   lane-fix could not execute the defeq reductions.
4. **A-2 + A-9** — refuse a goal emission with non-empty
   `universeVars` (emitter-side, two lines, loud), *and* hard-fail
   `has_goal_def == 0` on the plain replay path. Must land together
   with any F-5 fix.
5. **LIB-1/D-1** — write the differential row first (template:
   `differential/error_unreachable/test.saw`); one run settles
   reachability. Then move the `Except` inside the element or reject
   throwing `gen` bodies.
6. **RK-5** — give the CI harness a separate probe module that
   imports the emitted artifact, so the suite can catch regressions of
   1/2.
7. Regression rows for A-1, A-5, A-2 and S-1 under `saw-boundary/`,
   red today and green after; plus lint self-tests for A-6 and A-7.
8. Documentation corrections: A-3 (five sites, including the trust
   authority), the residual-trust sentence LIB-1 shows is backwards,
   the `Float`/`Double` faithfulness argument, the `divNat 2 0` ledger
   entry, `bvSExt` "stays axiomatic", and the F-1 "audited safe"
   verdict.

**Scope and framing.** Requested focus: *any* path by which an
unsound verification condition can reach production. Surface
concerns (filters, ergonomics) deliberately set aside; the question
throughout is whether the **proof terms and proof obligations the
backend constructs match SAW's semantics**, and whether the gate
that admits a Lean proof can be satisfied by something that does not
prove the emitted obligation.

**Method.** Six independent review lanes over the trust chain
(translator core calculus; name/convention mappings; recursion
seams; obligation contracts; Lean support library; replay trust
kernel), plus a directly-traced end-to-end pass on the goal
construction chain (`sequentToProp` → `writeLeanProp` →
`scNormalizeForLean` → emission → replay gate → evidence check).
Read-only; no builds were run (a full suite was executing
concurrently). Lean facts were established with the pinned
toolchain (v4.32.0) on standalone scratch files outside the
project, never through `lake`.

**Predecessors.** `2026-07-21_soundness-review.md` (F1 lint bug),
`2026-07-23_fidelity-review.md` (bvToInt class), and the same-day
`2026-07-24_soundness-audit.md` (R-1 replay hole, fixed). Findings
already reported there are not re-reported here except where this
audit shows the fix is incomplete.

---

## Verdict

**Two confirmed defects in the replay trust kernel, both of which
admit a false obligation, both demonstrated end-to-end against the
shipped `lean-check-core.sh`:**

- **A-1 (CRITICAL, live today).** A user `proof.lean` containing one
  extra `notation` line is accepted with `CHECK-OK` while proving
  only `True` — demonstrated on the false obligation
  `∀ x : Bool, x = !x`. Same class as R-1 (the closer↔goal binding
  is bypassed) through a different mechanism — Lean *name
  resolution* rather than the goal-presence flag — so the R-1 fix
  does not touch it. Live on the runtime replay path and the CI
  proof harness. It additionally defeats the in-statement
  obligation-binder (`by sorry`) detection.
- **A-2 (HIGH).** The R-1 fix hard-failed the goal-presence check on
  the completed-outline path but left the plain path as a silent
  `has_goal_def=0` branch. A goal emitted with a universe parameter
  (`def goal.{u0} :`) misses the detection regex and disables the
  binding gate entirely — a `proof.lean` that never mentions the
  goal is then accepted. Demonstrated end-to-end; the emitter-side
  reachability is plausible (see A-3) but not proven.

Both are gate defects, not translator defects. Everything traced on
the goal-construction side (below) held up: the sequent→Prop→closure
chain, the pre-translation constant folding, the adaptation
chokepoint, the Prop backstop, the obligation-binder mechanism, the
`Bool` case-order permutations, the constructor-order assertions, the
axiom allowlist, and the two-axiom trusted base.

## Severity summary

Findings prefixed `A-` are from the lead's lane (goal construction +
replay gate); `RK-`/`S-`/`LIB-`/`F-`/`D-` are from the five parallel
lanes. Every finding marked **[verified by lead]** was reproduced
independently against the shipped code on the pinned toolchain.

| ID | Sev | Lane | One line | Reachable today? |
|----|-----|------|----------|------------------|
| A-1 | **CRITICAL** | replay | user `notation "goal" => True` captures the closer-type probe; `CHECK-OK` on a proof of `True` against a false obligation | **YES** — runtime + CI; confirmed end-to-end. Independently found by lane-replay (RK-1) |
| A-5 | **CRITICAL** | replay | the probe accepts an inserted **coercion**, and the axiom audit then audits the wrong declaration — `native_decide` passes on a strict-tier row | **YES** — confirmed end-to-end **[verified by lead]**; lane-replay RK-2 |
| S-1 | **CRITICAL** | fix seams | the Class-F / Class-S productivity obligations are **erasable** on the completed-outline path — the only path that can accept them | **YES** — 10+ tracked rows use the path; no pin exists |
| A-2 | HIGH | replay | `has_goal_def=0` silent branch survives on the plain path; a `def goal.{u0}` emission disables the binding gate entirely — a proof that never mentions the goal is then accepted | **LIVE (narrow)** — checker defect confirmed end-to-end; lane-core produced a reachable `parse_core` trigger |
| A-9 | HIGH | goal emission | the `goal_holds` stub drops the goal's universe binders, so it proves `goal.{?u}` at one level instead of universally | same trigger as A-2 |
| F-5 | HIGH if reachable | sorts | `sort 0 → Type` **narrows** the quantifier: SAWCore admits `Prop ≤ sort 0`, Lean 4 has no term cumulativity, so the emitted goal is weaker on that instantiation class | no corpus witness; the one place sort handling loses ground |
| A-6 | HIGH | replay | `«debug».skipKernelTC` evades the lint — kernel checking off for the whole file | **YES** — lint + binding both **[verified by lead]**; lane-replay RK-3 |
| LIB-1 / D-1 | HIGH | lean lib + names | the `Except (Vec n α)` carrier hoists a per-element error to the whole vector; SAW's vectors are elementwise-lazy, so Lean **equates** computations SAW distinguishes. **One finding, derived independently from both ends** | Semantics confirmed both sides; emission path confirmed unobstructed; corpus incidence unproven |
| A-7 | Medium | replay | multi-line `@[ \n implemented_by …]` evades the attribute rule | **[verified by lead]**; lane-replay RK-4 |
| S-2 | Medium | fix seams | `saw_fix_unique_exists_raw` is not merely latent — it is emittable with an **honestly provable** obligation while SAW diverges | YES, with a concrete witness; no checker hardening can catch it |
| LIB-2 | Medium | lean lib | the five `*WithProof` primitives are **uninterpreted in SAW** but given values in Lean | YES — two tests already emit them |
| D-1 | Medium | names | `gen` → `genWithBoundsM` divergence (lane-names) | see lane section |
| A-3 | Medium | docs/gate | `polymorphismResidual` documented as a live refusal (and as the universe-soundness argument); does not exist | N/A — supplies A-2's trigger |
| RK-5 | Medium | harness | CI harness binds inside the user's own module; no `import Emitted` requirement | in-repo rows only |
| A-4 | Low-Med | printer | `prettyTerm` ignores `Prec` for `Sort` | only `sort k ≥ 1` |
| F-1 | Low(sound)/High(claim) | contracts | under-applied partial-op path emits an **ill-typed** artifact; the path has zero compiling witnesses despite being marked "audited safe" | loud, not silent |
| F-2 | Low | contracts | SEAMS-D3 **settled**: type-image collapse is real; `mkFloat`/`mkDouble` share a Lean body, making a SAW-invalid equation `rfl`-provable | needs hand-written SAWCore |
| F-3, LIB-3, LIB-4, S-3, RK-7, RK-8 | Low | various | see lane sections | — |

Reproduction material for A-1, A-2, A-5, A-6 and A-7 is in the appendix.

### Release gate

**A-1, A-5 and S-1 should block release.** Each independently allows
SAW to report a goal proved when the emitted obligation was not
proved. They are three *different* mechanisms — name resolution,
coercion insertion, and defeq-blindness — so fixing one does not
touch the others. A-6 removes the Lean kernel from the trusted base
and should be fixed in the same batch (it is a one-line `gsub`).

### The house pattern, seventh through ninth instances

The project's own review history records six translator bugs whose
root cause was "a syntactic side condition under-approximating the
semantic property it stood for." A-1/A-5 and S-1 are the same
pattern moved into the *gate*:

- A-1/A-5: `#check (goal_closed : goal)` is a syntactic proxy for
  "this theorem proves the emitted obligation". It is evaluated by
  the **elaborator**, in an environment the user's module extends —
  so the user controls the token table (A-1) and the coercion
  instances (A-5). `#check` adds no declaration and is therefore
  never kernel-checked (lane-replay's RK-9 structural note; the same
  is true of the drift and triviality probes).
- S-1: `rfl`-defeq of the emitted *value* is a syntactic proxy for
  "the obligation stated about the emitted term was discharged". The
  gap is every subterm the value does not definitionally depend on —
  and both `saw_stream_realize` and `saw_fix_bounded_choose` were
  written so that the obligation is exactly such a subterm.

## A-11 (SYSTEMIC) — the trust kernel asks `grep` questions that only Lean can answer

Almost every finding in the replay lane is an instance of one
architectural choice: **the trust kernel establishes properties of an
elaborated Lean environment by pattern-matching over Lean source
text.** Text matching and Lean's own view of the environment are
different functions, and every place they are used interchangeably is
a place they can disagree. They did, six times:

| Kernel rule | The grep | The property it stands for | How it broke |
|---|---|---|---|
| goal presence (`:118-131`) | `grep -E 'def goal *:'` | the emission defines the goal | misses `def goal.{u0} :` → gate silently off (**A-2**) |
| closer set (`:231-237`) | awk for `^theorem|lemma` | the theorems this module adds | misses `def hidden`, `@[simp] theorem`, namespaced closers (**A-5**) |
| goal binding (`:241-253`) | `#check (goal_closed : goal)` | this theorem proves the emitted obligation | elaborator-only, resolved in the user's token table and instance set (**A-1**, **A-5**) |
| placeholder policy (`:101-104`, `:183-188`) | `grep sorry` | does this depend on `sorryAx` | two rules disagree on the same bytes (**A-10**) |
| source lint (`proof-source-lint.awk`) | a hand-written lexer | this file declares no axiom and mutates no environment | `«debug»` (**A-6**), multi-line `@[...]` (**A-7**), `notation` unlisted (**A-1**) |
| drift (`:165-177`) | `#check … from rfl` | the completed goal is the emitted goal | elaborator-only; blind to non-defeq-relevant subterms (**S-1**) |

**Lean can answer all but one of these authoritatively**, and the
checker is already in a position to ask: it compiles the user's file
to `UserProof.olean` and then runs probe modules that import it.
Those probes can query the environment instead of the text —

- *what did this module declare?* — the constants `UserProof` adds
  beyond its imports. This subsumes the closer awk and closes A-5
  outright, because `hidden` is in that set regardless of the keyword
  used to introduce it.
- *what does it depend on?* — `#print axioms` over **every** added
  declaration, not only the ones spelled `theorem`. Subsumes the
  `sorry` text scan and A-10, since the real question was always
  `sorryAx`, never the token.
- *does it prove the goal?* — a real `theorem __replay_binding : goal
  := goal_closed` added to the environment, so the kernel checks the
  binding rather than the elaborator (already recommended for A-5,
  verified effective).
- *did it extend the environment?* — the added parser extensions,
  attributes and instances are enumerable. That is the property the
  awk lexer approximates, and it is what A-1/A-6/A-7 each slipped
  past.

**The honest exception.** One class genuinely cannot be checked from
inside Lean afterwards: **options that change how the module was
built**. `debug.skipKernelTC` (A-6) means the declarations in
`UserProof.olean` were never kernel-checked when added, and importing
a module does not re-check it — so an environment query run
downstream inherits the damage. For that class the answer is not a
better grep either: it is to stop the user controlling the build. The
checker already invokes Lean itself, so it can pass the options it
wants and refuse a file that sets any; or elaborate user content in a
context where the option cannot take effect. The source lint should
be a *backstop* for that narrow case, not the primary mechanism for
the other five rows.

**Why this belongs in the report as one finding.** Each row above has
its own fix, and those fixes are worth landing individually — but if
only the rows are fixed, the next rule added to the kernel will be
written as a grep too, and the seam reopens somewhere new. The
durable statement is: *a check in the trust kernel should query the
Lean environment, and fall back to source matching only where a
property is genuinely about the source or the build invocation — with
that exception named and argued in place.*

---

## A-1 (CRITICAL) — the closer↔goal binding probe is capturable by user-declared `notation`

**Confidence:** HIGH — reproduced end-to-end through the shipped
`lean-check-core.sh` (only the two `lake` invocations swapped for
the pinned raw `lean` v4.32.0; every check, awk script, grep and
probe is the shipped code). **Reachable:** YES, today, on the
product path.

### What breaks

Step 6 of the trust kernel is the *only* check that binds the user's
proof to the emitted obligation on the plain replay path:

- `saw-core-lean/replay/lean-check-core.sh:239-254` — builds
  `closer-type-probe.lean` containing
  `import Emitted` / `import UserProof` / `#check (goal_closed : goal)`
  and requires it to elaborate without error.

The probe resolves the identifier `goal` **in an environment that
includes the user's own module** (`UserProof` is the user's
`proof.lean`, copied at `:245`/`:258`). Lean 4 lets a module export
parser extensions to its importers, so the user can make the token
`goal` denote something else entirely:

```lean
notation "goal" => True
```

After that line, `goal` is a keyword atom denoting `True` in
`proof.lean` *and in every module that imports it* — including the
checker's own probe. `theorem goal_closed : goal := trivial` then
proves `True`, and `#check (goal_closed : goal)` type-checks
against `True`, not against the emitted obligation.

### The witness (confirmed)

Stage directory:

`Emitted.lean` (the fresh emission — a **false** obligation):
```lean
/- Code generated by saw-core-lean -/

noncomputable def goal : Prop :=
  (x : Bool) -> @Eq.{1} Bool x (not x)
```

`proof.lean` (the user's discharge):
```lean
import Emitted

notation "goal" => True

theorem goal_closed : goal := trivial
```

Result of running the shipped kernel:

```
CHECK-AXIOMS: 'goal_closed' does not depend on any axioms
CHECK-OK
KERNEL EXIT=0
```

Negative control — the identical file with the `notation` line
removed:

```
proof.lean:3:30: error: Type mismatch
  trivial
has type
  True
but is expected to have type
  goal
CHECK-FAIL: proof-does-not-elaborate
```

So the gate works exactly as designed, and one added line disables
it. Independently confirmed that the closer's real type is `True`:
under `set_option pp.notation false`, `#check @goal_closed` prints
`goal_closed : True`.

Per `saw-central/src/SAWCentral/Builtins.hs:1600-1607`, `ExitSuccess`
from the checker yields `SolveSuccess (LeanReplayEvidence …)` — SAW
reports the goal proved.

### Why every other gate passes

Each check was verified individually against the witness:

| Step | Check | Why it does not fire |
|---|---|---|
| 2 | placeholder policy on `Emitted.lean` | Emitted is the untouched fresh emission |
| — | `has_goal_def` (`:118-131`) | fresh emission has `noncomputable def goal :` → 1, so the gates *do* run — they simply pass |
| — | `GeneratedHarness` mention scan (`:138-143`) | witness never mentions it |
| 3 | anti-trivialization (`:149-155`) | probe imports **only** `Emitted`, so `goal` is the real goal; it is not closed by `rfl`/`trivial` → gate satisfied |
| 4 | completed-outline drift (`:165-178`) | `drift-check.lean` imports `Generated`+`Emitted` only — the notation never reaches it; an honest `completed.lean` passes drift normally |
| 4.5 | `sorry` scan (`:183-188`) | no `sorry` |
| 4.6 | `proof-source-lint.awk` (`:210-220`) | **`notation` is not on the denylist** (`proof-source-lint.awk:168-171` bans `axiom, macro, macro_rules, elab, elab_rules, run_cmd, run_tac, run_meta, run_elab, initialize, builtin_initialize, attribute, #eval, debug.*, @[extern/implemented_by/csimp]` — no syntax-declaring command). Verified: lint exits 0 on the witness. |
| 5 | proof elaborates (`:222-227`) | it does |
| 6 | closer contract (`:229-254`) | `closers` awk extracts `goal_closed`; the `#check` is captured |
| 7 | axiom audit + vacuity guard (`:256-292`) | `'goal_closed' does not depend on any axioms` — one audited line for one closer |

### A-1 also defeats the in-statement obligation defense

The emitted goal may legitimately contain `by sorry` obligation
binders (`Term.hs:2054-2058, 3340-3360, 3402-…`; sanctioned by the
placeholder policy at `lean-check-core.sh:101-104`). Amendment 3's
defense is that these remain *in-statement* and are therefore visible
to the closer's axiom audit. Verified that this defense works — and
that A-1 removes it:

- honest closer on a goal carrying an undischarged obligation binder
  → `sorryAx` / `CHECK-FAIL: axiom-outside-allowlist` (correct);
- same goal, closer captured by `notation` →
  `'goal_closed' does not depend on any axioms` / `CHECK-OK`.

The captured closer's type is `True`, so it never mentions `goal`
and `#print axioms` never traverses the goal's definition. A-1
therefore bypasses *both* the goal binding and the placeholder
detection — strictly worse than R-1.

### Both paths, both consumers

- **Plain replay path** — captured as above. This is the worst case:
  step 6 is the *only* proof↔goal binding on that path.
- **Completed-outline path** — also captured (confirmed with the
  kernel simulation). The user supplies an *honest* `completed.lean`
  (so the drift check passes normally) and puts the `notation` line
  in `proof.lean`; drift never sees it because `drift-check.lean`
  does not import the user proof module.
- **CI proof harness**
  (`otherTests/saw-core-lean/support/lean-proof-test.sh:437-458`) —
  captured, and *more* easily: the harness **appends** its
  `#check (goal_closed : goal)` / `#print axioms goal_closed` to a
  **copy of the user's `proof.lean`** (`proof.check.lean`), so the
  capture happens in the same file. Confirmed that `local notation`
  suffices there (it does *not* suffice on the replay path, since a
  `local` notation does not cross the module boundary — verified).

### Second, harness-only vector (same root cause)

Because the CI harness appends its checks to a copy of the user's
file rather than to an independent probe that imports the authority,
a `proof.lean` that simply **does not import the emitted artifact**
and declares its own `def goal : Prop := True` also passes there
(confirmed). The replay path blocks this one: its probe imports
`Emitted` itself, so a second root-level `goal` produces
`import UserProof failed, environment already contains 'goal' from
Emitted` (verified). This matters because it means the test suite
cannot catch an A-1-class regression.

### Also tested and *not* exploitable

- `export Decoy (goal)` to create a competing root-level `goal`:
  Lean 4.32 reports `Ambiguous term` and errors → gate holds
  (verified).
- A root-level `def goal` in a file that *does* import `Emitted`:
  duplicate declaration → error (verified).

### Recommended fix

Two independent changes; do both.

1. **Probe a name the user cannot mention.** Stage the fresh
   emission under a harness namespace on *every* path (not only the
   completed path) and make step 6
   `#check (goal_closed : <HarnessNS>.goal)`. The existing
   `GeneratedHarness` mention scan (`:138-143`) then blocks the
   capture — verified necessary: a dotted-atom
   `notation "GeneratedHarness.goal" => True` *does* capture a
   namespaced probe, so the namespace only works **because** the
   mention scan rejects user files containing that string. Prefer a
   per-call gensym namespace so the name is not derivable at all,
   and keep the mention scan.
2. **Ban syntax-declaring commands in proof-side files.** Add
   `notation`, `syntax`, `infix`, `infixl`, `infixr`, `prefix`,
   `postfix`, `binder_predicate`, `declare_syntax_cat`, and
   `export` as standalone tokens to `proof-source-lint.awk:168`.
   None has a legitimate place in a discharge file, and this is the
   same defense-in-depth reasoning that already bans `macro_rules`
   and `elab` (which are exactly the desugaring of `notation`).
   Consider `unif_hint` too — it was *tested and found not
   exploitable* against the drift `rfl` on v4.32.0 (Lean rejects the
   hint at declaration time in both shapes tried), but it is an
   elaborator-level defeq extension and belongs on the list.

   **Cost of the ban: zero.** Scanning all 119 `proof.lean` /
   `completed.lean` files in the tree, the only textual matches for
   these tokens are the English word "prefix" inside docstrings in
   three rows — which the lint already strips as comment content
   before matching. No current row would break.

Apply both to `lean-proof-test.sh` as well, and additionally make
that harness build its checks in a **separate probe file that
imports the emitted artifact**, rather than appending to a copy of
the user's file.

### Regression tests to add (must be red today)

- `saw-boundary/replay_reject_notation_capture` — the witness above,
  asserted REJECTED by `offline_lean_replay`, with the diagnostic
  pinned.
- A `trust-tier-selftest.sh` case for the same shape.
- A CI-harness negative row for the no-import decoy-`goal` vector.

---

## A-2 (HIGH) — a universe-parameterized goal silently disables the entire binding gate

**Confidence:** HIGH on the checker-side defect (demonstrated
end-to-end); the emitter-side reachability is plausible but not
proven with a SAW-level witness.

`saw-core-lean/replay/lean-check-core.sh:126-131`: on the
non-completed path,

```sh
has_goal_def=0
if grep -qE "$goal_def_re" "$STAGE/Emitted.lean"; then
    has_goal_def=1
fi
```

If that grep fails for any reason, steps 3 and 6 — the
anti-trivialization probe and the *entire* closer↔goal binding
gate — are skipped, and a `proof.lean` needs only to elaborate and
contain one named theorem with clean axioms. That is precisely the
"a 0 silently disables the gate" pattern the R-1 fix set out to
eliminate; the fix hard-failed the *completed* path
(`:119-125`) but left the plain path as a silent branch, even though
the same justification ("the replay path always emits exactly one
`def goal`") applies to both.

A concrete mechanism exists for the grep to fail. The regex is

```
^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goal[[:space:]]*:
```

and the emitted header is rendered by
`saw-core-lean/src/Language/Lean/Pretty.hs:253-265` as
`hsep (keyword ++ [nm'] ++ binderDocs ++ mtyDocs ++ [":="])` with
`nm' = prettyIdent nm <> prettyUnivs univs`
(`Term.hs:5475` passes `view universeVars state`). A goal emitted
with any universe parameter renders as `noncomputable def goal.{u0} :`,
which the regex does **not** match → `has_goal_def=0` → the binding
gate silently disappears. `universeVars` is populated by
`Convention.hs:530-542` whenever a `TypeSort k` with `k ≥ 1` reaches
`TypeCarrierPos` or `BinderPos`. See A-3: the gate that the
architecture doc claims prevents this does not exist.

Confirmed against the shipped kernel. Stage:

`Emitted.lean`:
```lean
noncomputable def goal.{u0} : Prop :=
  (a : Sort u0) -> (x : Bool) -> @Eq.{1} Bool x (not x)
```
`proof.lean`:
```lean
import Emitted

theorem totally_unrelated : 1 + 1 = 2 := rfl
```
Result:
```
CHECK-AXIOMS: 'totally_unrelated' does not depend on any axioms
CHECK-OK
```

Note this is *worse* than A-1: with `has_goal_def = 0` there is no
`goal_closed` requirement at all, so a proof file that never
mentions the goal admits it. Verified separately that
`grep -E "$goal_def_re"` returns no match on the
`def goal.{u0} :` line.

**Reachability of the trigger.** `Term.hs:294-340` takes the
`BinderPos`/`TypeCarrierPos` path — allocating a universe variable
into `universeVars` — precisely when a binder's type is a bare
`Sort k` with `k ≥ 1`. That is the shape
`README.md:45-46` says is "refused with `polymorphismResidual`" — a
refusal that does not exist (A-3). So the shapes the docs claim are
rejected are today *translated*, with universe parameters, into
exactly the emission that disables the gate. I did not construct a
SAW-level witness (that needs a SAW run, which was out of scope
here); **producing or ruling out one should be the first follow-up.**

**Fix:** make `has_goal_def == 0` a hard failure on the plain replay
path too (`fail "replay-emission-missing-goal-def"`), exactly as
done for the completed path. The replay driver always emits exactly
one goal def, so a 0 is a translator/renderer bug and must be loud.
Separately, derive goal-presence from the emitter (which knows it
emitted one `def goal`) rather than from a regex over rendered text.

---

## A-3 (Medium, documentation/soundness-claim drift) — `polymorphismResidual` does not exist

**Confidence:** HIGH.

`saw-core-lean/doc/architecture.md` describes `polymorphismResidual`
as a live gate in three places, including the soundness-boundaries
section:

- `:47` — in the pipeline diagram:
  `polymorphismResidual (gate: full term-tree walk; reject sort k>0)`
- `:124` — hosted in `SAWCentral/Prover/Exporter.hs`
- `:151` — listed under **Translator-time refusals**, "Each pinned by
  a regression test"
- `:169-172` — the universe-soundness argument:
  "`translateSort` maps every non-Prop SAW sort to Lean `Type`.
  Pre-`polymorphismResidual` this would weaken; **the gate enforces
  that only Type-0 binders reach emission.**"
- `saw-core-lean/README.md:45-46` — "Universe-polymorphic terms
  (`(t : sort 1) → …`) — refused with `polymorphismResidual`."

**There is no such identifier anywhere in the source tree** (grep
over the whole checkout returns only doc files; the archived
`doc/archive/2026-05-14_keep-kill-map.md:294-316` records that it
was already dead in May and recommended excising it).

Both halves of the `:169-172` argument are also stale against the
current code: `translateSort`
(`saw-core-lean/src/SAWCoreLean/Convention.hs:527-542`) does *not*
map every non-Prop sort to `Type` — `TypeSort 0 → Type`, and
`TypeSort k ≥ 1` becomes `Lean.TypeLvl k` at `ValuePos` or a
**freshly allocated universe variable** at `TypeCarrierPos`/
`BinderPos`. So the universe treatment is different from what the
doc describes, and the refusal it rests on is absent.

This is filed as Medium rather than tertiary because it is a
*soundness argument* in the authoritative architecture document
resting on a non-existent mechanism, and because it supplies the
trigger for A-2. It does not by itself establish that a sort-k>0
binder reaches emission — that is the open question below.

**Recommended:** either restore a real gate (and pin it with the
regression test the doc already claims exists), or rewrite
`architecture.md:47/124/151/169-172` and `README.md:45-46` to state
the actual current mechanism, and add a translator-side refusal for
any goal emission that would carry universe parameters (which also
closes A-2's trigger).

---

## A-4 (Low-Medium) — `prettyTerm` ignores precedence for `Sort`

**Confidence:** HIGH on the defect; reachability limited to the same
universe-level ≥ 1 region as A-2/A-3.

`saw-core-lean/src/Language/Lean/Pretty.hs:182-183`:

```haskell
    Sort s ->
      prettySort s
```

Every other constructor in `prettyTerm` respects the `Prec`
parameter (`parensIf (p > …)`); `Sort` drops it. `prettySort`
(`:104-110`) renders `TypeLvl n` as `Type n`, `TypeVar u` as
`Type u`, and `SortVar u` as `Sort u` — **multi-token** forms. In
argument position (`PrecAtom`, `Pretty.hs:170`) the emitted text
therefore parses differently from the AST: an intended
`f (Type 1) k` is printed as `f Type 1 k`, which Lean reads as `f`
applied to three arguments.

Verified on v4.32.0 that `#check g Type 1` and `#check g (Type 1)`
are different terms, and that the mis-parse produced a loud
application-type mismatch in the cases tried. It is not *guaranteed*
loud, though: any callee whose argument types happen to accept the
re-associated spelling would type-check as a different term.

`TypeLvl 0` renders as the single token `Type` and is safe, so this
is unreachable while every emitted sort is `Type 0`/`Prop` — i.e.
the trigger region is exactly the `sort k ≥ 1` shapes that A-3 shows
are no longer refused.

**Fix:** `Sort s -> parensIf (p > PrecApp) (prettySort s)` (or
always-parens for the multi-token forms). One line, no behavior
change on any current artifact.

Related, lower: `Ascription` (`Pretty.hs:198-202`) is only
parenthesized at `p > PrecLambda`, but a bare `a : T` is not a Lean
term at all — every unparenthesized rendering is a parse error
rather than a mis-parse, so this is loud today. Tightening it to
always-parens costs nothing.

## Surfaces traced and found sound (this audit's own lane)

These are reported because "this surface is sound, and here is the
reason" is a deliverable.

### Sequent → Prop → universally-closed term

- `SAWCentral/Proof.hs:678-694` `sequentToProp` builds
  `H1 → … → Hn → C` and **fails loudly** on multi-conclusion
  sequents; the empty-conclusion case becomes `… → EqTrue False`.
  Faithful.
- `SAWCentral/Prover/Exporter.hs:1305-1321` `writeLeanProp`
  universally closes the goal over its free SAWCore variables
  (`getAllVars` + `scPiList`). Universal closure is the correct
  reading of "must hold for all symbolic inputs"; a missed or
  misordered variable produces an ill-typed term or an unbound Lean
  identifier — loud either way, never a weaker statement.
- `SAWCentral/Proof.hs:227-240` `boolToProp` wraps a Bool-valued
  goal as `EqTrue b`, and `Prelude.sawcore:881-882` defines
  `EqTrue x = Eq Bool x True`, so the emitted Lean shape
  `@Eq (Except String Bool) <lhs> (pure true)` is the faithful
  image. Observed in `saw-core-lean/lean/demoProbe/eq/Emitted.lean`.

### Evidence handling

`SAWCentral/Proof.hs:1649-1657` checks `LeanReplayEvidence` with
`sequentSubsumes sc sqt' sqt` — the same discipline as
`SolverEvidence`. Replay evidence cannot be reused for a different
goal. (It is a non-recheckable trust token by design; that is
documented at `Proof.hs:1030-1038` and is not a defect, but it is
why A-1 matters: nothing downstream re-derives the guarantee.)

### The pre-translation constant-folding pass

`scLiteralFold` (`Exporter.hs:580-740`) rewrites the goal term
*before* translation, so a wrong rule silently changes the
obligation. Every rule was dispositioned against
`saw-core/prelude/Prelude.sawcore`:

| Rule | SAW authority | Verdict |
|---|---|---|
| `addNat`/`mulNat` | `:1097-1116` | exact |
| `subNat x y → if x≥y then x-y else 0` | `:1243-1253` (`ZtoNat (subNZ x y)`, `ZtoNat` sends negatives to `Zero`) | exact — truncated subtraction, correctly modelled |
| `expNat m n → m^n` | `:1119-1127` (outer recursion on `n`; `n=0 → 1`, `m=0,n>0 → 0`) | exact, including `0^0 = 1` |
| `minNat`/`maxNat` | `:1150-1155` | exact |
| `divNat`/`modNat`, **guarded `bn ≠ 0`** | `:1287-1297` | safe: SAW's `divModNat`/`posDivMod` give *nonzero* results at divisor 0 (e.g. `modNat 1 0 = 1`); the guard means those are never folded |
| `pred 0 → 0` | `:1383-1384` | exact |
| `doubleNat` | `:1258-1259` | exact |
| `equalNat`/`ltNat`/`leNat` | `:1131-1148` | exact |
| `intAdd/Sub/Mul/Neg/Eq/Le/Lt` on Integer literals | standard | exact |
| `intToNat`, **guarded `nv ≥ 0`** | `:2105-2106` (`intToNat x == max 0 x`), `Prims.hs:1337-1341` | safe (negative case simply not folded) |
| `ite`/`iteDep` with literal condition | `:464-480` (`Bool#rec1 p f1 f2 b`) | exact — True selects the first branch |

The `Lambda`/`Pi` cases deliberately do not fold binder types; that
is a completeness limit, not a soundness one. Caching by `termIndex`
is safe under SAWCore hash-consing.

### The Nat-literal macros

`SAWCorePrimitives.lean:90-99` — `one_macro = 1`, `bit0_macro n = 2*n`,
`bit1_macro n = 2*n+1`, `natPos_macro n = n` — match
`Prelude.sawcore:963-967` (`One`/`Bit0 = 2n`/`Bit1 = 2n+1`) and
`:1088-1091` (`Nat = Zero | NatPos Pos`). The SAW→Lean value map on
`Nat` is a bijection onto `ℕ`.

### The Prop backstop

`Convention.hs:800-802` argues `DVarValue` wrapping is safe because
`Except String P` at `P : Prop` is ill-typed in Lean 4. Verified as a
Lean fact: `Except.{u,v}` requires `β : Type v = Sort (v+1)`, and
`Sort (v+1) ≡ Sort 0` has no solution in Lean's level arithmetic, so
the bad instantiation fails at elaboration. The backstop holds.

### The in-statement obligation-binder mechanism

`withLocalProofObligation` (`Term.hs:2069-2085`) emits

```lean
let h_X_obligation_ : Prop := <the obligation>;
let h_X_ : h_X_obligation_ := ((by sorry));
<consumer h_X_>
```

into the goal statement. Three properties were verified mechanically
on v4.32.0:

1. `#print axioms goal_closed` **does** traverse into the type's
   definition and reports `sorryAx` — so an undischarged obligation
   binder cannot survive the axiom audit (amendment 3's claim holds).
2. In the completed-outline flow, substituting a real proof for the
   `(by sorry)` keeps the completed goal **definitionally equal** to
   the generated goal (proof irrelevance on the `Prop`-typed binder),
   so the drift `rfl` accepts the substitution while still rejecting
   any change to the *proposition*. This is the intended and correct
   discharge vehicle.
3. Consequently the axiom audit is clean exactly when the user has
   supplied a genuine proof of the obligation.

The mechanism is sound. One coherence note: because of (1), a goal
carrying an obligation binder can never be discharged through the
*plain* `proof.lean`-only replay path — only through a completed
outline. `Term.hs:3352-3360` says the obligation is "discharged in
the proof row"; that is true only of the completed-outline row, and
is worth stating explicitly in the docs.

### The unmapped-identifier default

`SpecialTreatment.hs:212-226` `defaultTreatmentFor` is `UseReject` —
an identifier with no mapping cannot be silently emitted as a bare
name that might resolve against an `open`ed support-library
namespace. This is the right default and is load-bearing.

### The adaptation chokepoint

`adaptTo` (`Term.hs:4471-4492`) is the single point where a
translated term changes representation. Enumerating its table: the
only value-changing adaptation is `BindingRaw → BindingWrapped` via
`Pure.pure`, which is a total injection and loses nothing; every
other admissible pair is the identity; everything else throws
`ForbiddenAdaptation`. **Runtime → raw is deliberately absent**, so
there is no point-adaptation that can discard an `Except` error case
— the only way to consume a wrapped value at a raw position is an
error-preserving `Bind.bind` continuation built by the bind-chain
emitters. No adaptation in the table is non-injective, which is the
property that matters for an emitted equation.

### Error propagation in the translator

There is no `catchError`, `tryError`, or `<|>` anywhere in
`saw-core-lean/src/` — every `RejectedPrimitive`,
`ForbiddenAdaptation`, `UnsoundRecursor`, etc. propagates out of the
translation monad, and `Exporter.hs` turns a `Left` into
`throwTopLevel`. The three `fromMaybe` uses (`Term.hs:364, 378,
3505`) are wrap-override and name defaults, not error handling. So
"loud failure over silent divergence" holds structurally at the
translator boundary.

### Bool case order

`SAWCorePreludeExtra.lean:35-89`: SAWCore declares `Bool` True-first
and Lean declares it false-first, so a faithful realization must
permute. `iteDep p b fT fF = Bool.rec fF fT b`, `ite a b x y =
Bool.rec y x b`, and `iteM`'s `Except.ok v => Bool.rec y x v` all
permute correctly. The four `@[simp]` reduction lemmas are
`rfl`-proved, so they cannot change provability.

### Constructor-order assertions

`saw_ctor_order` (`SAWCoreCtorOrder.lean:33-45`) is a real
elaboration-time check (`iv.ctors == declared`, `throwErrorAt`
otherwise) with negative `#guard_msgs` self-tests at `:70-85`, so it
cannot silently become a no-op. On the emitter side,
`recordCtorOrderAssertion` (`Term.hs:4255-4275`) is invoked at the
single `Foo.rec` head-emission site (`:4371`), is deduplicated per
datatype, and **refuses loudly** for any datatype/constructor without
a fixed fully-qualified Lean target — so no recursor leaves the
translator with unchecked constructor-order trust.

### The trusted base

`saw-core-lean/lean/CryptolToLean/*.lean` contains exactly two
`axiom` declarations — `vecToBitVec_bitVecToVec` and
`bitVecToVec_vecToBitVec` (`SAWCorePrimitives.lean:600, 604`) —
and no `sorry`, `native_decide`, `unsafe`, `partial def`,
`opaque` declaration, `@[implemented_by]`, or `@[extern]`. Both
axioms are round-trip identities on the MSB-first encoding and are
decidable at every concrete width. The claim in `architecture.md`
that the trusted base is exactly these two holds.

One stale comment: `SAWCorePrimitives.lean:625-628` says `bvSExt`
"Stays axiomatic", but `:883-884` defines it as an ordinary
`noncomputable def` through `BitVec.signExtend` with no axiom and no
cast. Post-Phase-9 drift; harmless, but it misdescribes the TCB.

### The axiom allowlist

`replay/axiom-audit.awk:59-76` compares **exact** fully-qualified
names against a fixed five-entry list; the `native-eval` tier
pattern is fully anchored
(`^goal_(holds|closed)\._native\.bv_decide\.ax_[0-9_]+$`); an
unknown tier prints `UNKNOWN-TRUST-TIER` (which itself makes
`bad_ax` non-empty → reject) *and* clears the tier; a declared
but unused tier prints `TRUST-TIER-UNUSED`. The vacuity guard at
`lean-check-core.sh:281-292` requires exactly one audited line per
closer. Confirmed by inspection that the shipped Lean library
contains exactly the two sanctioned `axiom` declarations
(`SAWCorePrimitives.lean:600, 604`) and no `sorry`,
`native_decide`, `unsafe`, `partial def`, `implemented_by`, or
`extern`.

---

---

# Lane findings

Six lanes ran in parallel over the trust chain. Their full reports are
summarised here with the lead's independent verification noted where
it applies. Two lanes independently rediscovered A-1, which is
corroboration rather than duplication.

## Replay trust kernel (lane-replay)

### A-5 (CRITICAL) — the probe accepts a coercion; the audit then inspects the wrong declaration

**[verified by lead, end-to-end]** — lane-replay RK-2.

`lean-check-core.sh:248-253` uses `#check (goal_closed : goal)`. A
type ascription in Lean inserts **coercions**. The user supplies:

```lean
import Emitted

def hidden : goal := by
  show <the goal body, copied verbatim>
  native_decide

theorem goal_closed : True := trivial

instance : CoeT True goal_closed goal := ⟨hidden⟩
```

Verified on v4.32.0:

```
#check (goal_closed : goal)   ⇒  hidden : goal          exit 0
#print axioms goal_closed     ⇒  'goal_closed' does not depend on any axioms
#print axioms hidden          ⇒  [hidden._native.native_decide.ax_1]
```

The checker prints only the middle line. `def hidden` is invisible to
the closer awk (`:231-237` matches only `theorem`/`lemma`), and Lean's
"use `theorem` instead of `def`" output is a *warning*, so it survives
the error grep and the exit-0 test.

**What this breaks is the axiom allowlist itself.** The proof of the
goal is real, but it is by native evaluation — the Lean *compiler*
enters the trusted base on a row whose evidence record says strict
tier. Any other non-allowlisted axiom hides identically. This is the
one way to get native-evaluation trust onto a strict row; the tier
machinery itself is correct (lane-replay confirmed the pattern is
anchored and that `native_decide`'s axiom name does *not* match it).

**Fix — verified effective.** Replace the `#check` with a real,
kernel-checked declaration and audit *it*:

```lean
theorem __replay_binding : goal := goal_closed
#print axioms __replay_binding
```

Verified: this reports
`'__bind' depends on axioms: [hidden._native.native_decide.ax_1]`
⇒ `axiom-outside-allowlist`. It also blocks the A-1 witness with a
type mismatch, and makes the binding kernel-checked rather than
elaborator-only.

### A-6 (HIGH) — `«debug».skipKernelTC` evades the lint

**[verified by lead]** — lane-replay RK-3.

`proof-source-lint.awk:170` matches `debug\.[A-Za-z]` literally. Lean
accepts escaped name components, so `«debug».skipKernelTC` is the same
`Name`. Verified:

| input | lint | meaning |
|---|---|---|
| `set_option debug.skipKernelTC true in …` | rc=1, caught | correct |
| `set_option «debug».skipKernelTC true in …` | **rc=0, empty** | evades |
| `set_option «debugZZ».skipKernelTCzz true` | — | Lean: `Unknown option 'debugZZ.skipKernelTCzz'` — proving the escaped spelling really binds |

With the option set, kernel type-checking is skipped for every
declaration in the file, leaving the elaborator as sole checker —
i.e. the thing the whole invariant is anchored on is removed. Rated
"trust-base breach" rather than "confirmed unsoundness": neither
lane-replay nor the lead built a false theorem on top of it.

**Fix:** one line — `gsub(/[«»]/, "", out)` before the denylist match
at `:168`. This also hardens every other rule against `«axiom»`-style
spellings.

### A-7 (Medium) — multi-line `@[...]` evades the attribute rule

**[verified by lead]** — lane-replay RK-4. `proof-source-lint.awk:171`
is per-line by construction, so

```lean
@[
  implemented_by evilImpl]
def f (x : Nat) : Nat := x
```

passes the lint (verified rc=0). Same shape for `csimp` / `extern`.
These matter for native-evaluation trust. Fix: track attribute
brackets in the lexer state, or accumulate `out` across lines.

### RK-5 (Medium) — the CI harness binds inside the user's own module

`lean-proof-test.sh:437-457` appends `#check (goal_closed : goal)` to
a **copy of the row's `proof.lean`**, so both names resolve in the row
author's scope. A row that simply omits `import Emitted` and defines
its own `goal` passes everything. This is an accidental-miss class
(an honest row that forgets the import silently stops being checked),
and it means the suite cannot catch an A-1/A-5-class regression. It is
also genuine consumer drift: `lean-proof-test.sh:272-276` claims
identical semantics with the trust kernel "by mechanism, not
discipline" — true for the axiom audit, false for the binding.

### RK-7 / RK-8 (Low)

- `lean-check-core.sh:278-280` tests only emptiness of the
  axiom-audit awk output; an awk hard-error yields empty output and
  reads as a clean audit. This is exactly the hazard the lint
  invocation at `:212-215` was hardened against (`LC_ALL=C` + explicit
  `lint_rc`); the asymmetry looks unintentional. One line to fix.
- `Builtins.hs:1494` gates cache reuse on marker *existence* only;
  staged contents are never re-hashed. Anyone with write access to
  `~/.cache/saw-core-lean/lean-<fp>/` can substitute the support
  library — adding *lemmas*, which the allowlist audit cannot see.
  `SAW_LEAN_ROOT` substitutes both the library and the checker script.
  Defensible as a dev override, but residual-trust should say so.

### RK-9 (structural, underlies A-1/A-5)

Every gate binding user content to the authority — the binding probe
(`:241-253`), the drift probe (`:168-177`), the triviality probe
(`:150-152`) — is a `#check`. `#check` adds no declaration and is
therefore **never kernel-checked**; each verdict rests on the
elaborator alone, in an environment the user's module extends (token
table, instances, coercions). A-5's fix converts the most important of
the three into a kernel-checked obligation; the same treatment is
worth considering for the other two.

### Rules lane-replay checked and found CORRECT

The exact-name allowlist (no prefix/substring matching anywhere); the
tier pattern's anchoring and prefix-pinning, confirmed tight against
`native_decide`'s real axiom name; unknown/stale tier sentinels; the
`#print axioms` multi-line parse (fails closed on a mid-name split);
the vacuity guard; closer discipline; axiom transitivity; `export`
aliasing (fails closed with `Ambiguous term` — the lead confirmed
this independently); `unif_hint` (Lean validates hints at declaration
time and rejects them — the lead confirmed this independently in two
shapes); the impossibility of user files influencing elaboration of
the emitted statement (Emitted is a separate module compiled first);
no user-controlled imports; the `GeneratedHarness` ban; the R-1 fix on
the completed path; fail-closed stub-strip drift; exit-status plumbing
(only RK-7 drops one); the Haskell consumer admitting only on
`ExitSuccess` with no stdout success-marker parsing; runtime tiering
always strict; the lint lexer against the F1 class; and staging
coverage consistency.

**Important correction to the A-1 fix.** Qualifying the probe does
**not** work: lane-replay compiled a user module containing
`notation "_root_.goal" => True` and the qualified probe still passed.
Notation atoms are arbitrary strings, so any spelling the probe uses —
including `«goal»` — can be claimed as a token, because the probe
necessarily imports the user's module and inherits its token table.
**The fix must be the lint denylist plus the kernel-checked binding
theorem, not a probe rename.**

## Recursion seams (lane-fix)

### S-1 (CRITICAL) — the fix/stream productivity obligations are erasable

The soundness story for both wrapped `Prelude.fix` classes is
*entirely* the per-instance obligation: the realizations are by
construction a particular value and equal SAW's meaning only if
`H_prod` holds. Two mechanisms were supposed to force the discharge.
The lead's `sorryAx` result shows the first blocks the plain path
outright — so the completed-outline **drift check is the sole gate**,
and that gate is `rfl`-defeq, which is blind to anything the emitted
value does not definitionally depend on.

Confirmed by reading the two realizations:

- `SAWCorePrimitives.lean:1417-1421` — `saw_stream_realize α x0 step
  mkfn _h := Pure.pure (saw_stream_unfold α x0 step)`. The body
  mentions **neither `mkfn` nor `_h`**, so the emitted term reduces to
  a value independent of both the element function and the obligation.
- `SAWCorePrimitives.lean:1333-1337` — `saw_fix_bounded_choose … :=
  saw_fix_bounded_iter_from n α (Classical.choice h.seed) body n`.
  `Classical.choice : Nonempty a → a` takes a **Prop-typed** argument,
  so by proof irrelevance the term is defeq for *any* inhabitant of
  `Nonempty (Vec n α)`.

Consequently a completed outline may write the reduct directly —
never stating `total`/`lookback`/`faithful` — and drift `rfl` passes,
no `sorry` appears, and the axiom audit is clean.

**The crisp discriminator**, and why `saw_mkStream_choose` and the raw
fix contract are immune: `Classical.choice`'s argument is proof-
irrelevant ⇒ **erasable**; `Classical.choose {a} {p : a → Prop}`
carries the obligation predicate as a *type-level implicit* ⇒
**binding**. `saw_mkStream_choose` (`:1440-1443`) and
`saw_fix_choose_raw` use `choose`; the two defective ones use
`choice` or ignore the proof entirely.

**Not merely adversarial.** The existing acceptance row
`otherTests/saw-core-lean/proofs/cryptol_module_rec_ones/completed.lean:29-40`
hand-copies the emitted element function into
`RecOnesDischarge.streamFn` and proves `rec_ones_h_prod` about *that
copy*. If the copy drifts — `subNat i 2` instead of `subNat i 1` —
every gate stays green, because nothing compares the copy to the
emitted lambda. Same family as R-1's accidental variant.

**Reachability: live.** 10+ tracked `proofs/*/completed.lean` rows use
this path, including the R3b Class-S acceptance row.
`trust-tier-selftest.sh` has no case for obligation erasure.

**Fix direction:** either route the Class-S value through
`Classical.choose` of an `∃ t, …` obligation the way
`saw_mkStream_choose` does (making the obligation defeq-visible),
and/or add a presence gate requiring every
`h_*obligation_ : (Prop) := (<expr>)` line of the *authority* emission
to appear verbatim in `completed.lean` with a present, non-`sorry`
proof binder. The latter catches both variants.

**Caveat, flagged by lane-fix itself:** the defeq reductions were not
executed (builds forbidden). The reasoning is standard — plain
non-`irreducible` defs, `rfl` at default transparency, definitional
proof irrelevance for `Prop` — and the lead independently confirmed
the two realization bodies by reading them. Running the two witnesses
through the real `lean-check-core.sh` is a ~10-minute red-before/
green-after exercise and should be the first action.

### S-2 (Medium) — `saw_fix_unique_exists_raw` is reachable *and honestly dischargeable*

LB-1 was previously recorded as latent. lane-fix produced a witness:

```
enable_experimental;
let probe = parse_core "fix Nat (\\(n : Nat) -> mulNat n 0)";
write_lean_term "P" [] [] "emitted.lean" probe;
```

Path: `Term.hs:2693` → `classifyFixShape` returns `FixUnrecognized`
→ `shouldWrapBinder Nat = False` (`Convention.hs:847`, `DNat`) →
`Term.hs:2726` → `lowerFixProofObligation` (`:3325`). The emission
type-checks because `mulNat` is in `leanOpaqueBuiltins` and both its
formals and result are `DNat` ⇒ raw, so the body emits as
`fun (n : Nat) => mulNat n 0 : Nat -> Nat`.

The obligation is provable in three tokens —
`⟨0, rfl, fun y h => h.symm⟩` — because `Nat.mul y 0` reduces to `0`.
But SAW's meaning is **⊥**: `mulNat` recurses on its *first* argument
(`Prelude.sawcore:1108-1113`), so `let x = mulNat x 0 in x` must force
`x` to compute `x`.

This is qualitatively worse than S-1: S-1 is fixable by hardening a
checker; **S-2 is not**, because the contract is extensional and
cannot observe operational divergence. Every check goes green
honestly.

lane-fix also recorded *why* ordinary recursive Cryptol functions do
not hit this: their value-domain codomain is `Except String T`, and
the constant-error family `κ_s = fun x => Except.error s` is a fixed
point of essentially every bind-sequenced translated body, so
uniqueness fails for exactly the divergent shapes. **That protection
is accidental, not designed** — it rests on `Except String` having
infinitely many inhabitants, and it does not extend to `DNat` /
`DRawProp` / `DRawType`. The code's "believed corpus-unreachable"
comment (`Term.hs` near `:3323`) understates why it currently holds.

### S-3 (Low) — Class-F recognizer over-approximates; `inZip` is dead code

`FixRecognizer.hs:301-351`: `scanRecUses` is entered as `go False elt`
and every recursive call passes `False`, so the `inZip` flag is
invariantly `False` and the `Right True` branch at `:307` is
unreachable. Consequently the zip arm at `:310` fires *anywhere* in
the element term, with no requirement that the zip be consumed by an
`at` at the inner binder. A body like `foldr … (zip a b K K rec ys)`
— where output element `i` depends on all of `rec` — classifies
`FixClassF` while SAW's fix is ⊥. Not a soundness defect *on its own*
(the `lookback` field is unprovable for such a body), but it converts
an intended emission-time named rejection into a check-time
undischargeable obligation, violating the module's own stated
reject-when-unsure discipline — and that matters more given S-1
undermines "the obligation is the backstop."

### Seams lane-fix checked and found SOUND

`saw_fix_bounded_productive` ⇒ unique pure fixed point (stabilization
argument re-derived independently); `saw_stream_single_productive` ⇒
the SAW stream; no off-by-one in either lookback window;
`shouldWrapBinder` routing for recognized classes (Vec/Stream reach
`classifyDomain`'s `DValue` arm, so they can never fall through a
failed case guard onto the raw path); gate↔lowering agreement;
loud reject paths (no `catchError` anywhere); total `fix_unfold`
rejection; `MkStream` totality (genuinely binding, via
`Classical.choose`); `streamScanl`; over-applied fix; and no name
capture in the emitted let-chains.

## Lean support library (lane-lib)

### LIB-1 / D-1 (HIGH) — the wrapped-vector carrier equates computations SAW distinguishes

**Found independently by both lane-lib and lane-names**, with
different witnesses and the same root cause. This is the most
significant *translator-side* finding of the audit.

SAW's vectors are element-lazy. `Prims.hs:861-871` `genOp` builds
`V.generateM` over **`delay`ed thunks**, and `atWithDefaultOp`
(`:897-908`) forces only the selected thunk. So an `error` in a slot
that is never read is never observed.

The Lean carrier for a value-domain `Vec n T` is
`Except String (Vec n T')`, which **cannot represent** "an error in
one slot and good values elsewhere". `genWithBoundsM`
(`SAWCorePrimitives.lean:1032-1035`) is `Vector.ofFnM`, which
sequences every element through `Except` and short-circuits — and
this is denotational, not an evaluation-order artifact: the `Except`
bind case-splits on each element, so the kernel reduces the whole
vector to `Except.error msg`.

**The adaptation `Vec n (Except String T') → Except String (Vec n T')`
is non-injective**, and the collapsed value appears on *both sides* of
emitted equations. This is precisely the non-injective adaptation the
audit charter asks about.

lane-names' witness (`T = Vec 8 Bool`):

```
A = at 2 T (gen 2 T (\(i:Nat) -> ite T (equalNat i 1) (error T "e") (bvNat 8 7))) 0
B = at 2 T (gen 2 T (\(i:Nat) -> ite T (equalNat i 1) (error T "e") (bvNat 8 9))) 0
```

- SAW: `A = 0x07`, `B = 0x09` (index 0 is read; the index-1 thunk
  holding `error` is never forced) ⇒ `Eq T A B` is **FALSE**.
- Lean: both sides are `Except.error "e"` ⇒ the emitted equation
  **closes by `rfl`**.

lane-lib's witness avoids `error` entirely, using only `at`, `gen` and
an out-of-range index, and is deliberately order-independent (a single
failing index on both sides, so `Vector.ofFnM`'s short-circuit
behaviour does not matter).

Same class, lower reach: `genM` (`:1040`), `vecSequenceM` (`:1174`,
used for SAW array literals), `atRuntimeCheckedM`, `foldrM`/`foldlM`,
and `sawLet` (`SAWCorePreludeExtra.lean:101-105` matches on `x` and
returns the error, whereas `Prelude.sawcore:21-22` `sawLet _ _ x f =
f x` beta-reduces and discards `x` when `f` ignores it).

**Explicitly NOT affected**, each checked individually: `iteM`
(discards the unselected branch — the branch analogue of this bug, and
it is handled *correctly*), `foldrM`/`foldlM` accumulators,
`atWithDefaultM` (SAW's `atWithDefault` forces the vector too).

**The residual-trust document states this backwards.**
`doc/2026-05-02_residual-trust.md:496-503` says the eager `Except`
carrier can "surface an error a lazy evaluation never touches… outside
[the fenced region] the obligations are unprovable, not wrong." When
*both* sides eagerly surface the *same* message, the obligation is not
unprovable — it becomes trivially TRUE in Lean while FALSE in SAW.
The byte-exact error messages chosen to stop Lean *over-distinguishing*
are exactly what lets Lean **over-equate**. That sentence should be
corrected regardless of what the reachability investigation concludes.

**Reachability: strongly indicated, not confirmed.** Every ingredient
is on the live path (`gen`→`genWithBoundsM`, `at`→the bounds contract,
`ite`→`iteM`, `error`→`saw_throw_error`); `at` and `ite` are in
`leanOpaqueBuiltins` so they survive normalization; and `scLiteralFold`
has **no** `at (gen …)` fold rule. Neither lane could run the pipeline.
**No test pins this class**: all 117 differential rows were checked —
`error_unreachable` covers only `ite`-branch laziness, `fix_error_elem`
covers a *reached* error. There is no row where SAW succeeds lazily and
Lean errors eagerly.

**First action:** write that differential row (template:
`differential/error_unreachable/test.saw`). One run settles it.

### LIB-2 (Medium) — the `*WithProof` family is uninterpreted in SAW but interpreted in Lean

`atWithProof`, `genWithProof`, `updWithProof`, `sliceWithProof`,
`updSliceWithProof` are all declared `primitive` at
`Prelude.sawcore:2419-2438` with **no body**, and a repo-wide search
finds zero implementations — no `constMap` entry, no `Concrete.hs`
override, nothing in What4/SBV/RME. Their only SAW semantics is their
type. The Lean helpers give them values, so e.g.
`atWithProof 3 Bool 0b101 2 pf = False` is `rfl`-provable in Lean
while SAW must satisfy it for *all* interpretations. **The Lean
statement is strictly weaker than the SAW obligation.**

Reachable today: `Contracts.hs:170-212` wires all five, and
`obligations/vector_at_with_proof/` and `obligations/vector_gen_with_proof/`
already emit them. Mitigating: the chosen interpretations are the ones
the Prelude comments document. This is a documented-trust item that is
**absent from the residual-trust catalog** and should be added, or the
helpers gated the way `IntMod` now is.

### Sound, with the arguments (lane-lib)

- **The two axioms are TRUE, not merely unproven** — hand-verified in
  both directions including `n = 0`. This matters more than
  enumerating them: a false bridge axiom would void every downstream
  bv theorem.
- Zero `sorry`/`native_decide`/`unsafe`/`opaque`/`partial def`/
  `implemented_by`/`extern`, and — answering the charter's question
  directly — **zero `instance`/`deriving` declarations**, so the
  "`Inhabited` makes a partial realization silently total" attack has
  no surface here. `EmptyVec` is defined by `Fin 0` elimination
  precisely so it needs no inhabitant.
- All 27 `@[simp]` sites are either `@[reducible]` defs or fully
  proven theorems; the two `_proofs` files (~2,300 lines, *not*
  covered by the 2026-07-23 review) are sound by construction —
  nothing false is *possible* there, since the kernel checks it.
- `Either`/`Maybe` are declared `Sort (max 1 u v)`. **The `max 1` is
  load-bearing**: at `u = v = 0` they land in `Type`, not `Prop`. Had
  they been `Sort (max u v)`, `natCompareLe : Either (IsLtNat m n)
  (IsLeNat n m)` would land in `Prop` and its two branches would
  collapse by proof irrelevance, destroying the comparison. This is
  exactly the proof-irrelevance leak the charter asks about, and it is
  correctly avoided.
- Every bv primitive dispositioned against `Prim.hs` at the *edge*
  class: width 0, shift/rotate ≥ width, all-zero clz/ctz,
  most-negative/−1 signed division, sign-crossing conversions.
  `bvLg2` hand-evaluated at x = 0..8. The 2026-07-23 `bvToInt` fix
  verified in place and **siblings hunted for across every conversion
  and comparator — none found**.
- `iteDep`/`ite` permute SAW's True-first order correctly *and* are
  kept opaque by `Exporter.hs:1234` so normalization cannot expose a
  bare `Bool#rec` in SAW's order — the single most dangerous
  silent-swap site in the library, properly fenced.
- `saw_fix_bounded_productive` checked for **vacuity** at `n = 0`:
  `total` is non-vacuous there (`Vec 0 α` is a singleton, so
  `∃ w, body (pure #v[]) = pure w` forces a real constraint), and
  `lookback` uses strict `j < i`. `seed` is discarded with
  irrelevance *proven* (`SAWCorePrelude_proofs.lean:902`).
- `saw_unsafeAssert` expands only to `rfl`/`decide`/`simp`/`omega` —
  no `native_decide`, no `sorry` fallback, no fabricated term.

### LIB-3 / LIB-4 (Low)

`IntMod n := Int` means a *bound* `IntMod` variable ranges over
representatives rather than residues. Harmless in positive `∀`
position (Lean's domain is a superset ⇒ stronger statement); unsound
only in a negative position (an `IntMod`-quantified hypothesis or an
existential), and no such emitted shape was found. Distinct from the
open F1 (`n = 0` totalization). — `saw_ctor_order` compares
constructor *names* in order but not arity or field order within a
constructor; the four guarded types have self-tests, `PairType` /
`RecordType` / `UnitType` / `EmptyType` do not. Defence-in-depth gap,
not a hole.

## Obligation contracts (lane-contracts)

**Headline: no MISSING and no WEAKER obligation exists.** All 12
partial-op preconditions and all 6 checked-application preconditions
are **EXACT** (two deliberately STRONGER at Cryptol's degenerate
widths, which is the safe direction). The operand-index audit found
no bound stated on the wrong operand anywhere in the table. The
missing-obligation sweep was done by enumerating SAW's *sources* of
partiality rather than spot-checking: the only Prelude partiality
introduced via `error` is `at` (`Prelude.sawcore:1564`), and it is
covered.

**The emitted proof-term surface is exactly four shapes**
(`grep 'Lean.Tactic'` returns three construction sites, plus
`Eq.refl`), and none can close a false goal:

1. `checkedEvidenceScript` (`Contracts.hs:743-753`) — `assumption` /
   `omega` / a `simp only` set in which **every lemma is a `rfl`-lemma
   or a reducible unfolding**, then `skip` → `all_goals sorry`. No
   `decide`, no `native_decide`, no `Fin.mk _ (by omega)`, no `cast`,
   no `Classical`.
2. `unsafeAssertProofScript` (`Term.hs:2065-2067`) — `rfl` or sorry.
   Since SAW's `unsafeAssert` is an axiom SAW grants *unconditionally*,
   a Lean-`rfl`-closable instance is strictly *less* trust than SAW
   itself takes.
3. `proofObligationPlaceholder` — plain `sorry`; claims nothing.
4. `Eq.refl` at the argument's universe, for `Prelude.Refl` — the
   carrier is read from the SAW type argument, not guessed.

Grepping `Term.hs` for `cast`, `Eq.mpr`, `Fin.mk`, `absurd`,
`Classical`, `decide`, `trivial`, `propext`, `Subsingleton` returns
**no emission sites**.

Also verified sound: the dispatch chain is closed (a contract-bearing
ident can never fall through to its total `mapsTo` target — every
remaining arity rejects with a named error); the one admitted
under-application, `at`, is the dominant Cryptol indexing shape and is
handled correctly with SAW's own error string; the `h_gen_bounds_`
binder is never fabricated for an unguaranteed bound (only two
insertion sites, both backed by a genuine `Fin.isLt`); runtime-computed
indices are sequenced through `Bind.bind` so the obligation is about
exactly the index used; no name capture; and the user-supplied
skips/renaming hole does not touch the admitting path (`ImportedName`
only, and `offline_lean_replay` passes empty lists anyway).

### F-2 (Low) — SEAMS-D3 is SETTLED, in the affirmative

The previously-unconfirmed type-image collapse is **real**, with two
witness families, and **found independently by lane-contracts and
lane-names**:

- `Integer` and `IntMod n` for every `n` → `Int`. Not exploitable:
  every `IntMod` operation carries `n` explicitly and normalizes via
  `Int.fmod`, cross-modulus equalities are ill-typed in SAW, and
  `IntMod 0` is separately gated.
- `Float`, `Double` → `Int × Int`, both `@[reducible]`. **This one is
  exploitable.** `Prelude.sawcore:2153/2160` declare two *distinct*
  abstract types, and `:2156/2163` declare `mkFloat` and `mkDouble` as
  two *distinct uninterpreted* primitives — with **zero** simulator
  realizations. The Lean side gives both the same body
  (`SAWCorePrimitives.lean:294-302`), so:
  - `Eq (sort 0) Float Double` — not derivable in SAW; `rfl` in Lean.
  - `Eq Float (mkFloat m e) (mkDouble m e)` — not valid in SAW's model;
    `rfl` in Lean.
  - `mkFloat` becomes injective in Lean, so SAW-unprovable
    disequalities become `decide`-provable.

  The justifying docstring ("SAW has no operations to make this
  binding observable, so any inhabited concrete type is faithful")
  is wrong on two counts: `mkFloat` *is* an operation, and `Eq` is the
  observer at both the type and the value level. "No *executable*
  observer" is a weaker property than "no *equational* observer". A
  faithful realization needs two distinct opaque Lean types and an
  uninterpreted constructor.

  Reachability is low (Cryptol floats elaborate to `Cryptol.TCFloat`,
  never `Prelude.Float`; this needs hand-written SAWCore), but
  `obligations/float_mk_float/` and `float_mk_double/` already emit
  these names, and the anti-trivialization probe catches only the
  *unquantified* form — `∀ m e, mkFloat m e = mkDouble m e` is closed
  by `fun m e => rfl`.

### F-1 (Low for soundness / High for the claim) — the under-applied partial-op path is unvalidated

`lowerPartialOpRuntimeWrapper` returns `BindingFunction`, which
records nothing about the *formals'* representation, so
`topLevelDefConvention` annotates the definition **raw** for a
`Nat -> Nat` SAW type. The repository's own pinned golden
(`saw-boundary/partial_operation_obligations/under_applied_partial.log.good:10-11`)
shows the result:

```lean
noncomputable def UnderAppliedPartialProbe : Nat -> Nat :=
  divNat_runtimeM (Pure.pure (natPos_macro one_macro))
```

`divNat_runtimeM : (x y : Except String Nat) -> Except String Nat`, so
the RHS has type `Except String Nat -> Except String Nat`, which is
not `Nat -> Nat`. `grep -r "_runtimeM"` over the whole tree returns
**exactly this one line** — so the path that
`doc/2026-07-18_underapplied-partial-op-wrapper.md:6` marks
"AUDITED — SAFE-WITH-CONDITIONS" has **no compiling Lean witness
anywhere**, and its single pinned artifact does not type-check.

Not a soundness defect (Lean rejects it, and the lead's `adaptTo`
result confirms nothing downstream can silently absorb the `Except`),
but the "audited safe" verdict is not backed by evidence.

### F-3 (Low-Medium) — division-wrapper error messages have no SAWCore backing

`atRuntimeCheckedM` throws `"at: index out of bounds"` — byte-identical
to SAWCore's own string (`Prelude.sawcore:1564`) — so that collision is
faithful. The division wrappers differ: `divNat_runtimeM` throws
`"divNat: division by zero"`, a message **SAWCore never produces**,
and `divModNat` is a *defined* function, hence total under definitional
unfolding. So `divNat x 0 = divNat y 0` for `x ≠ y` is FALSE under the
definitional reading and TRUE under the Lean lowering. The design
deliberately takes the evaluator reading (`Prims.hs:333, 717-724`
overrides the SAWCore definition with Haskell `divMod`, which crashes
at zero), under which both sides are ⊥ and the collision is standard
bottom-identification. Both readings are defensible; unlike the `at`
case there is no SAWCore error string to appeal to. Contained by the
full-arity obligation and by F-1.

## Name mappings and conventions (lane-names)

**~150 entries dispositioned FAITHFUL against the authority**, with
the argument recorded for each. Highlights of what was checked rather
than assumed:

- **The Vec↔BitVec bridge is exact**, so the two trusted axioms are
  *true statements*: `vecToBitVec` is byte-for-byte the recurrence of
  `Prim.hs:127-128`, and `bitVecToVec`'s `getMsbD` is literally
  `Prim.hs:124`'s `bvAt (BV w x) i = testBit x (w-1-i)`. Big-endian
  orientation confirmed on both sides.
- **No guessing catch-all on the live path.** The `Cryptol` module map
  has only four entries, so every `ec*` primitive — `ecNumber`,
  `ecFromTo`, `ecDemote`, `ecEq`, `ecZero`, `ecPlus` — *rejects
  loudly*. The charter's `ecNumber`/`ecDemote` width-handling concern
  does not exist here by construction.
- Operand order verified on **asymmetric** inputs, not just symmetric
  ones, for `bvugt`/`bvuge`/`bvsgt`/`bvsge` (which flip operands onto
  `ult`/`ule`/`slt`/`sle`).
- `intDiv`/`intMod` → `Int.fdiv`/`Int.fmod` (**floor**, matching
  Haskell `div`/`mod` in `Concrete.hs:213-214`), *not* the truncating
  `Int.div`/`Int.mod` — the correct choice, all four sign
  combinations checked.
- `IsLeNat n m` means `n ≤ m` with the parameter first, matching Lean's
  `Nat.le n m` argument order exactly; `IsLtNat m n = IsLeNat (Succ m) n`
  matches `Nat.lt` definitionally.
- `divModNat` pair order correct (`.0` = quotient, `.1` = remainder).
- The Rational family is faithful because every SAW observer is
  reduction-invariant (cross-multiplication, floor division), so
  Lean's reduced `Rat` agrees observationally with SAW's *unreduced*
  pairs.
- `mkDouble : Int → Int → Float` correctly mirrors SAW's own odd
  declaration — the "no silent corrections" rule applied correctly.

### D3–D6 (informational)

- **D3** — `divNat 2 0`: three different semantics exist at divisor
  zero. SAWCore's *definitional* unfolding is total and gives `1`;
  the simulator crashes; Lean gives `0`. Fully gated today, but the
  fidelity-review ledger records only the simulator's, and a future
  "SAW is undefined there anyway, let's totalize" decision would be
  made on a false premise. One-line ledger correction.
- **D4** — `findSpecialTreatment'`'s `ImportedName{} → UsePreserve`
  (`SpecialTreatment.hs:176`) is the table's one *guessing* arm,
  contradicting the module's own "no escape hatch" principle at
  `:187-226`. Mitigated: the live dispatch rejects `ImportedName`
  unless renamed/skipped, and the emitted alias is name-mangled
  `__saw_realizes_<zencoded>` so it cannot shadow anything.
- **D5** — no guard against emitted declarations shadowing the ~130
  implicitly-opened short names. Lean resolves a current-namespace
  declaration in preference to an `open`ed one **silently**, not as an
  ambiguity error. The `mapsToQualifiedTie` fix addresses only
  Lean-*root*-scope ties, which fail loudly. No live instance (the
  auto-emit set is disjoint from the opened names), but it is a
  missing fence.
- **D6** — `("Bit", mapsTo … "Bit")` (`SpecialTreatment.hs:571`) is a
  dead entry: no `Prelude.Bit` identifier exists. Cryptol's surface
  `Bit` elaborates to `Bool`. An entry no test can exercise and no
  authority backs.

## Core calculus and gates (lane-core)

### A-2's trigger is REACHABLE — question (B) answered

lane-core could not rule it out, and produced a concrete route.
`universeVars` is appended only by `translateSort` at
`BinderPos`/`TypeCarrierPos` with `TypeSort k ≥ 1`
(`Convention.hs:529-542`), from exactly two callers: a binder whose
type is a bare `sort k ≥ 1` (`Term.hs:294-342`), and — the one that
matters — **any `sort k ≥ 1` literal appearing as an FTermF node
anywhere in the term, including argument position** (`Term.hs:4299`).

Corpus evidence: `grep 'def goal\.{'` over the whole tree returns
nothing, and the only universe-parameterized goldens come from
`write_lean_saw_module`, not the goal path. But `parse_core` is a
supported SAWScript primitive whose output feeds
`prove_print`/`offline_lean`:

```
parse_core "Eq (sort 1) (sort 0) (sort 0)"    -- sort-1 literal in argument position
parse_core "(t : sort 1) -> Eq t x x"          -- bare sort-1 binder
```

The first traces: App → arg is `FTermF (Sort (TypeSort 1))` →
`Term.hs:4299` (`BinderPos`) → `Convention.hs:537-542` →
`Lean.SortVar "u0"` pushed onto `universeVars` → the body mentions
`Sort u0` so `usedUniversesInDecl` keeps it → `Term.hs:5479` →
`Pretty.hs:253-254` renders `noncomputable def goal.{u0} : Prop :=`.

**Neither `writeLeanProp` pin fires.** The arity pin counts the
`sort 1` binder on both sides, so it matches; and `telescopeFpMismatch`
requires both fingerprints to be non-`FpOther` (`Term.hs:5408`) while
`sawBinderFp` returns `FpOther` for a sort — a wildcard.
`polymorphismResidual`, which would have blocked the binder route,
does not exist.

**⇒ A-2 is LIVE, not latent**, via a supported front door. Given the
checker's binding gate silently disables on that rendering, the right
0.01 action is to **refuse** a goal emission with non-empty
`universeVars` — a two-line change, and loud — rather than attempting
to prove unreachability.

### A-9 (new, HIGH) — the `goal_holds` stub drops the universe binders

`Lean.hs:134-137` builds the stub from the **bare** `nameStr` with no
universe binders:

```lean
noncomputable def goal.{u0} : Prop := …
theorem goal_holds : goal := by sorry
```

Lean instantiates `goal`'s universe with a fresh metavariable resolved
by unification, so `goal_holds` proves `goal.{?u}` at **one** level
rather than universally over `u0` — a strictly weaker theorem than the
emitted goal, silently. Any fix for A-2 must cover both halves.

### A-3 confirmed, with more citations, and the replacement judged sound

lane-core independently confirmed `polymorphismResidual`'s absence and
adds two citations the lead missed — `contributing.md:132` and `:239`,
and, most importantly, **`doc/2026-05-02_residual-trust.md:574`, the
trust authority itself, still pins the gate.** That is the one that
matters for an audit-record-carried soundness argument. Also:
`architecture.md:170`'s "translateSort maps every non-Prop SAW sort to
Lean Type" is **false as written** — only `TypeSort 0` maps to `Type`.

The *replacement* is sound, and lane-core verified both load-bearing
properties: no collapse remains, and per-binder freshness is real
(the memo is keyed on `VarName`, whose `Eq`/`Ord` compare `vnIndex`
only, so two distinct SAW binders never share a universe — the L-10
contract holds). Direction of strength is right:
`∀ {u} (a : Sort u), P a` implies SAW's `∀ (a : sort k), P a`.

One accidental caveat: `scFun sc a b = scPi sc wildcardVarName a b`
gives **every** non-dependent SAW arrow the same `VarName 0 "_"`, so
two anonymous `sort k ≥ 1` binders in one term share a universe
variable through the memo, contradicting that memo's own docstring.
Still sound (a shared-universe `∀` still implies the concrete-sort
one), but accidental.

### (D) confirmed — one recursor-head emission site

`grep '\.rec'` over the package returns exactly one construction
(`Term.hs:4372`), immediately after `recordCtorOrderAssertion` at
`:4371`, and it covers partial applications (the head is translated
before the `fullySupplied` test) and bare non-applied recursors. Two
caveats: the assertion does not constrain *field* order within a
constructor (matching lane-lib's LIB-4), and `@Eq.rec` reaches
emission through a hardcoded path (`Term.hs:3741-3746`) that skips
`translateFTermF` entirely.

### F-5 (HIGH if reachable) — `sort 0 → Type` *narrows* the quantifier

This is the one place in the sort handling that **loses** ground
rather than gaining it, and it is not what A-3's missing gate covered.

SAWCore admits `Prop ≤ sort 0` cumulativity — `instance Ord Sort` at
`saw-core/src/SAWCore/Term/Functor.hs:65-68` is `PropSort <= _ = True`,
and `scmSubtype` **applies it as subsumption**
(`saw-core/src/SAWCore/Term/Certified.hs:1429-1430`). So a SAW binder
`(a : sort 0)` *can* be instantiated at a proposition. Its Lean image
is `(a : Type)` (`Convention.hs:528`), and `P : Prop` is `Sort 0`
while `Type 0 = Sort 1` — with no term cumulativity in Lean 4, that
instantiation class is simply absent. **The emitted goal is strictly
weaker than the SAW obligation on it.**

Note this is *k = 0*, so `polymorphismResidual` — which gated `k > 0`
— would not have caught it either; restoring the gate does not close
the universe question.

Reachability: lane-core grepped every `def goal : Prop` body across
all 190 goldens for `(x : Type)` binders — **zero hits**;
specialization monomorphizes goals. `(a : Type)` binders do appear in
*defs* (`test_records.t10.lean.good:9`, `test_poly_eq.module.lean.good:11`),
where the narrowing is benign because SAW never instantiates a Cryptol
type variable at a proposition. Neither telescope pin catches it
(`sawBinderFp` returns the `FpOther` wildcard for a sort).

**Fix:** emit `Sort u` (fresh universe) for sort-0 binders too —
uniform with the `k ≥ 1` path, and `u := 0` *does* cover `Prop` — or
refuse a sort binder in a goal telescope. Tension with A-2: the first
option makes universe-carrying goals common, so it must land together
with the goal-side universe fix.

### F-2 / F-3 (Medium) — the ctor-order assertion does not pin what the head resolves to, nor field order

- **F-2:** the recursor head is emitted **short** (`translateIdentToIdent`
  shortens under `isImplicitlyOpened`, `Term.hs:4364`), producing
  `@Stream.rec`, while `recordCtorOrderAssertion` emits the
  **qualified** `saw_ctor_order CryptolToLean.SAWCorePrimitives.Stream …`
  (`Term.hs:4270`). The emitted file `open`s `SAWCorePrimitives` and
  Lean core has a root-scope `Stream`, so `@Stream.rec` is genuinely
  ambiguous and resolved by overload-by-elaboration. If it ever
  resolved to the core one, **the assertion would still pass while
  checking a different inductive.** The assertion's own docstrings
  (`AST.hs:203-206`, `Term.hs:526-531`) argue qualification is
  mandatory *precisely because* short names collide with `Stream` —
  and then do not apply that reasoning to the head being guarded.
  One-line fix: emit the head qualified too.
- **F-3:** `SAWCoreCtorOrder.lean:40` compares `iv.ctors` — names in
  order — but not arity or **field order within a constructor**. Note
  the coverage inversion: 5 of the 6 asserted datatypes have a single
  constructor, i.e. the assertion is vacuous exactly where the
  field-order hazard lives. For a Cryptol record `{a : [8], b : [8]}`
  (α = β), a field swap typechecks while swapping every projection.
  This matches lane-lib's LIB-4 from the library side.
- **F-3b (Low):** `@Eq.rec` reaches emission through a hardcoded path
  (`Term.hs:3741-3746`) that skips `translateFTermF`, so it carries no
  assertion — an unasserted exception to the stated invariant. `Eq` is
  single-constructor and lane-core verified the emitted argument order
  against Lean's `@Eq.rec` on a real golden, so no defect follows.

### F-6 / F-7 (Medium / Low-Med) — name hygiene is delegated to Lean's typechecker

`reservedIdents` (`Convention.hs:482-492`) is Lean keywords plus
`Prop Type Sort by do return`. It does **not** contain `Vec`, `Bool`,
`Nat`, `Eq`, `Except`, `String`, `Pure`, `Bind`, `Num`, `Stream`,
`coerce`, `saw_throw_error`, … — all of which the emitter writes as
bare short names into the same file. Trace:
`llvm_fresh_var "Vec" (llvm_int 8)` → abstracted by `scPiList` →
`escapeIdent` passes `Vec` through (alphanumeric, and
`leanReservedWords` stops at `Type`/`Sort`/`Prop`) → a Lean binder
`Vec` shadowing the support-library `Vec` throughout a goal body full
of `Vec n Bool`. In practice essentially every instance fails loudly
on a type error — but **the disjointness is accidental, not
structural**, and the dotted variant has no such guarantee (a local
`Pure` turns `Pure.pure` into generalized field notation). F-7 is the
same posture for Cryptol/SAWCore def names, which bypass `escapeIdent`
entirely (`CryptolModule.hs:49`, `SAWModule.hs:100,103` — contrast
`Lean.hs:169`, which *does* escape). A Cryptol def named `pred`/`zip`/
`seq` lands inside the emitted `namespace` where Lean prefers the
namespace-local name, silently rebinding that primitive for the rest
of the namespace. Fix: seed `unavailableIdents` from the enumerable
set of bare names the emitter can produce.

### A-10 (Low, fail-closed) — the two `sorry` rules contradict each other on the completed path

Raised by lane-core from the emitter side and lane-replay from the
checker side; neither lane owned it.

`unsafeAssertProofScript` (`Term.hs:2067`) is
`(first | rfl | skip); all_goals sorry`, so the literal token `sorry`
remains in the emitted **source** even when `rfl` discharges the goal
and no `sorryAx` appears in the term — witness
`test_arithmetic.t11.lean.good:111`. A source-text scan and an axiom
scan therefore give **different answers on the same artifact**.

The checker has two rules that disagree about this:

- `lean-check-core.sh:101-104` scans `Emitted.lean` leniently,
  exempting exactly this form (`| skip); all_goals sorry));`).
- `lean-check-core.sh:183-188` scans user files with **zero
  tolerance** (`grep -qn 'sorry'`).

On the completed path `Emitted.lean` *is* `completed.lean`
(`Builtins.hs:1581-1582`), so both rules apply to the same bytes and
the zero-tolerance one wins. Consequence: **a goal carrying a
sanctioned in-statement `sorry` cannot be discharged through the
completed path** unless the user also rewrites the tactic text (which
is legitimate — the elaborated term is unchanged, so drift still
passes by proof irrelevance — but nothing documents it).

Fail-closed, so this is incompleteness rather than unsoundness, and
it is the *third* place this audit found where a rule's syntactic
proxy and its semantic intent diverge. Worth reconciling: either make
the emitted tactic not mention `sorry` when the `rfl` alternative is
expected to fire, or apply the same exemption list to the user-file
scan.

### F-8 / F-9 (Low-Med / informational)

`mkDefinitionWith`'s `combineBinders` (`Term.hs:3560-3562`) takes the
lambda binder's type annotation with the Pi's result type, and the two
are translated by predicates the code explicitly says can disagree
(`Term.hs:4629-4650`). A binder-*name* disagreement is loud; a
binder-*type* disagreement is silent. **Not on the goal path** (for
`writeLeanProp` the `_` fallback fires and the goal is emitted
verbatim), but it is on `write_lean_term` / `write_lean_cryptol_module`,
whose defs proofs then import. — `SAWModule.hs:185-187` passes
`InjectCodeDecl "Lean"` text into the emitted file verbatim with no
validation or escaping: an unaudited text-injection seam in an
otherwise fully-structured emitter, not reachable from user Cryptol
today.

### A-4 confirmed independently, and the rest of the printer audited

lane-core derived the `Sort` precedence defect statically as its F-1
and could not settle whether Lean's level parsers consume greedily —
the lead's v4.32.0 result settles it, and lane-core upgraded the
severity accordingly. It is the **only** case in `prettyTerm`
producing multi-token output at `PrecAtom`. Reachable via the same
`parse_core` route as A-2, so a `parse_core` sort-1 goal trips both
defects at once.

Every other constructor was audited against `Prec` and found correctly
guarded — App, Pi (nested arrows parenthesize), Lambda, Let (the
layout gotcha implemented on *both* the RHS and the type annotation),
ExplVar/ExplVarUniv, IntLit (always parenthesized), List, StringLit
(escapes cover the three characters that affect parsing), Tactic (both
tactic strings are newline-free, so no group-flattening hazard). Two
structurally-unguarded-but-safe-today cases: `Ascription` is **dead
code** (only consumption sites exist — worth deleting so it cannot be
reintroduced), and `NatLit` is bare at `PrecAtom` so a negative
literal would render `f -5` (every construction site is non-negative).
Layout: `prettyDecl` wraps declarations in `nest 2`, so no wrapped
continuation line can reach column 0 and be misread as a command
boundary — verified against the goldens.

---

## Appendix — reproducing A-1, A-2, A-5, A-6 and A-7 without a SAW run

Because a full suite was running concurrently, no `lake build` /
`cabal` invocation was made. The trust kernel was exercised with its
own source, with only the two `lake` calls replaced:

```sh
sed -e 's|lake env lean "$@"|"$LEANBIN" "$@"|' \
    -e 's|build_out=$( ( cd "$PROJ" \&\& "${TO\[@\]}" lake build ) 2>\&1 )|build_out=$( true )|' \
    saw-core-lean/replay/lean-check-core.sh > core-sim.sh
export LEANBIN=~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean   # the pinned toolchain
bash core-sim.sh "$PWD/proj" "$PWD/stage"
```

Every grep, awk script (`axiom-audit.awk`, `proof-source-lint.awk`),
probe file, and control-flow branch is the shipped code; only the
support-library build (irrelevant to these findings — the witnesses
import nothing from it) and the `lake env` wrapper were bypassed.
The individual awk scripts were additionally run standalone against
the witnesses, and every Lean fact was checked on v4.32.0.

Re-running these as real rows once the suite is idle is worthwhile
confirmation, but the mechanism does not depend on the substitution.

## Open / not settled by this lane

- Whether a sort-`k ≥ 1` binder can actually reach goal emission
  today (the reachability half of A-2/A-3).
- Lane results from the five parallel reviewers (support library,
  recursion seams, name mappings, obligation contracts, core
  calculus) — folded in below as they land.
