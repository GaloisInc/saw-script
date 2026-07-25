# Plan: from syntactic to semantic checks in the replay trust kernel

**Date:** 2026-07-24. **Status:** PLAN — no code changes yet.
**Origin:** finding A-11 of `2026-07-24_soundness-audit-2.md`, plus
the in-session verification pass recorded below.

**Thesis.** The trust kernel currently establishes properties of an
*elaborated Lean environment* by pattern-matching over *Lean source
text*. Those are different functions. Every place they are used
interchangeably is a place they can disagree — and they have now
disagreed seven times (R-1, A-1, A-2, A-5, A-6, A-7, S-1). The
durable fix is not a better regex: it is to **ask Lean the question
the rule is actually about**, and to fall back to source matching
only where the property is genuinely about the source or the build
invocation — with that exception named and argued in place.

---

## 1. Threat model (read this first)

The goal is **not** "prevent all cheating." A user runs SAW on their
own machine, against their own proof files, with write access to the
support library, the checker script, and the cache. Anyone in that
position can make the tool say anything. Designing against them is
unachievable and would buy nothing, because they could equally well
just claim the goal was proved.

What the trust kernel is actually for, in priority order:

### T1 — Accidental self-deception (PRIMARY)

An honest user whose proof **silently stops being checked**. This is
the threat that matters, it is the one that has actually occurred,
and every finding in both audits has an accidental variant:

| Finding | The adversarial story | The accidental story that is the real risk |
|---|---|---|
| R-1 | doubled-namespace decoy def | an honest `abbrev goal` or namespaced outline ⇒ binding gate silently off |
| A-1 | `notation "goal" => True` | a `notation` written for readability captures the probe |
| A-2 | crafted universe-param goal | a `parse_core` goal renders `def goal.{u0}` ⇒ gate silently off |
| S-1 | obligation deliberately erased | a completed outline hand-copies the element function and the copy **drifts** (already live in `cryptol_module_rec_ones`) |
| RK-5 | decoy `goal` in the row | an honest row **forgets `import Emitted`** and stops being checked |

Against T1, a check that fails **loudly and wrongly** is far better
than one that passes silently. This ranking is why "hard-fail rather
than branch" is the recurring fix.

### T2 — Second-party review (WHY ADVERSARIAL RESISTANCE MATTERS)

The artifact must mean something to someone who did **not** write it:
a reviewer, CI, an auditor, a downstream consumer of
`LeanReplayEvidence`. Here the proof author and the party relying on
the check are different people, so author-controlled bypasses are
real. This is the only sense in which "adversarial" is the right
frame — not user-vs-tool, but **author-vs-reviewer**.

Under T2, A-5 is the sharpest finding in either audit: it puts
`native_decide` trust onto a row whose evidence record says *strict
tier*. The evidence lies to the reviewer.

### T3 — Explicitly OUT OF SCOPE

Named here so the boundary is honest rather than implied:

- **Anyone with write access to the toolchain, the support library,
  the checker, or the cache.** `SAW_LEAN_ROOT` substitutes both
  library and checker by design; RK-8's cache-marker weakness lives
  here. These are dev-override affordances, not defects — but
  `2026-05-02_residual-trust.md` must **say so**, which it currently
  does not.
- **A malicious `lean-toolchain` / a compromised Lean.** The kernel
  is the trusted base by construction.
- **Proof-irrelevance-based "cheating" that Lean itself sanctions.**
  If two proofs of a `Prop` are interchangeable, that is Lean's
  semantics, not a hole.

### The viability rule

Harden as far as is *viable*: a hardening earns its place if it
(a) closes a T1 accidental variant, or (b) closes a T2
author-controlled bypass, **and** (c) costs no false rejections on
honest input. Where (c) fails, prefer a loud, documented refusal over
a silent weakening — and record the refusal as a known limitation
rather than pretending the surface is covered.

---

## 2. Evidence: what the syntactic rules actually did

Verified in-session against the **shipped** kernel with real `lake`
(the audit's own reproductions used a raw-`lean` substitution; these
did not):

| Check | Result |
|---|---|
| A-1 witness (`notation "goal" => True`) through `lean-check-core.sh` | **`CHECK-OK`** on a proof of `True` against the false obligation `∀ x:Bool, x = !x` |
| A-2 witness (`def goal.{u0}`) through `lean-check-core.sh` | **`CHECK-OK`** for `theorem totally_unrelated : 1+1=2` — a proof that never mentions the goal |
| A-5's proposed fix vs the A-1 witness | `theorem __replay_binding : goal := goal_closed` **elaborates, kernel-checks, reports no axioms** ⇒ the report's claim that it blocks A-1 is **wrong**; the lint half is load-bearing |
| S-1(a) `saw_stream_realize α x0 step mkfn h = Pure.pure (saw_stream_unfold α x0 step)` | **`rfl`** — obligation fully erasable |
| S-1(b) `saw_fix_bounded_choose … h = saw_fix_bounded_iter_from … (Classical.choice ⟨v⟩) …` | **`rfl`** — seed erasable by proof irrelevance |
| A-6 `«debug».skipKernelTC` / A-7 multi-line `@[…]` / A-1 `notation` vs the lint | all three **evade** (rc=0, empty) |
| LIB-1 two-witness differential | SAW: `7` and `9`. Lean: both `Except.error "e"`; the SAW-**false** equation `ObservedA = ObservedB` proves with axioms **`[propext, Quot.sound]` — both on the strict allowlist** |

The pattern is uniform: **the rule's text proxy was satisfiable
without the property it stood for.**

---

## 3. The categories these findings stand for

Fixing eleven findings one at a time guarantees a twelfth. Each
finding is an *instance* of a category, and several categories admit
a **mechanical, complete** closure — an enumerable audit or a
checkable invariant — rather than a per-bug patch. Those are worth
far more than the individual fixes.

Ranked by whether the category can be closed wholesale:

### C1 — "A `0` silently disables the gate" — CLOSEABLE, mechanical

*A recognizer returns don't-know, and the failure branch **skips the
check** instead of failing.*

Instances: R-1 and A-2 (`has_goal_def=0` ⇒ binding gate off), V-H1
(no sidecar ⇒ any error passes), V-H2 (absent-only ⇒ empty emission
passes), RK-5 (no `import Emitted` ⇒ row stops being checked).

**Closure:** a structural invariant over the trust path — *no
conditional in a gate may have a branch that omits the gate.* Every
`if <recognizer>` whose else-branch skips a check must instead
`fail`, or carry an in-place argument for why the skip is sound.
This is enumerable today: there are on the order of a dozen such
conditionals across `lean-check-core.sh`, `lean-proof-test.sh`,
`lean-obligation-test.sh` and `lean-negative-test.sh`. Auditing all
of them once, and adding the rule to `contributing.md` as a review
gate, closes the category — not just the two known instances.

### C2 — Doc claims a gate that does not exist — CLOSEABLE, mechanical

*A soundness argument rests on a named mechanism that was deleted,
renamed, or never enforced.*

Instances: A-3 (`polymorphismResidual` — cited in the **trust
authority**, absent from the source since May), LB-2 (`missingDocs`
"enforced", only warns), F-1 ("audited safe", zero compiling
witnesses), DOC-1 (case count), the residual-trust sentence LIB-1
shows backwards, and — sharpest — `saw_stream_realize`'s own
docstring asserting "the proof argument is consumed" over a body that
ignores it.

**C2 has two halves, and only one is closed.**

*Half A — an identifier that must exist.* Closed mechanically by
`support/doc-claim-lint.sh` (landed 2026-07-24; 256 identifiers over
8 maintained docs, wired into the suite). Beyond A-3 it immediately
found four more dead claims, three of them in the trust authority.

*Half B — a claim about BEHAVIOUR, at either polarity.* NOT closed,
and the more dangerous half, because nothing breaks when such a claim
becomes false:

- *Positive* — "the proof argument is consumed so an undischarged
  obligation is loud" (`saw_stream_realize`'s docstring, over a body
  that ignores it). Verified false by execution: S-1.
- *Negative / forward-looking* — HELP-1: `Interpreter.hs:5303-5307`
  tells users `offline_lean_replay` is "NOT AVAILABLE in this
  release — this command currently always fails with a diagnostic",
  and `:5295` promises SAW-side discharge "will arrive", eight days
  after it did. Found by an independent agent AFTER both six-lane
  audits; audit-1's lane-sawside verified the interpreter *wiring*
  and never read the *text*.

Half B is partly mechanisable and worth doing: a **stale-promise
lint** over user-facing help text and docstrings, flagging
`not yet` / `will arrive` / `NOT AVAILABLE` / `always fails` /
`reserved` and requiring each to carry a justification the reviewer
re-checks. It cannot decide truth, but it can force a periodic
re-read of exactly the sentences that rot silently — which is where
both instances above lived. Note the asymmetry that makes this
category insidious: an over-claim ("this gate protects you") is
caught by an audit looking for holes, while an under-claim ("this
feature does not work") is caught by nobody, because no one goes
looking for a feature they have been told is absent.

**Closure (half A):** a doc-claim linter. Extract backticked identifiers from
the soundness-claim docs (`residual-trust`, `architecture`,
`README`, `contributing`) and assert each exists in the source tree;
fail the suite when one does not. A-3 would have been caught by ~20
lines. The docstring variant needs a human rule — *a docstring
asserting a code property is a claim and must cite what enforces
it* — but the identifier half is fully mechanical, and it is the
half that reached the trust authority.

### C3 — Fail-open on tool failure — CLOSEABLE, mechanical

*A subprocess crashes, produces empty output, and empty reads as
clean.*

Instances: RK-7 (axiom-audit `awk` hard error ⇒ empty ⇒ pass), and
the already-fixed F1 hardening (`LC_ALL=C` + explicit `lint_rc`) —
which is precisely the same bug caught a year earlier in a sibling
call site and **not generalized**.

**Closure:** every subprocess capture in the trust path checks exit
status **and** output. Enumerable by grep over `$( … )` captures;
about a dozen sites. Add to the review gate.

### C4 — Guard with no mutation that catches it — CLOSEABLE, mechanical

*A guard exists, is believed to protect something, and has never been
observed to fire.*

Instances: V-H1 (four of six negative probes were **already** vacuous
— their subjects had been retired from the library and they were
passing on `unknown identifier`), V-H2, the axiom-audit vacuity guard
(fixed 2026-07-20 after the same realization).

**Closure:** the project rule "every guard ships with a mutation it
demonstrably catches" already exists but is **unenforced**. Make it
structural: enumerate the guards in the trust path and require a
`trust-tier-selftest.sh` case per guard, with the suite failing on an
unmatched guard. That converts a convention into a gate — the same
move LB-2 shows we have not been making.

### C5 — Non-injective translation ⇒ a false equation becomes provable — CLOSEABLE by enumeration, high effort

*Two SAW-distinguishable things map to one Lean thing, and both sides
of an emitted equation land on the collapsed image.*

Instances: LIB-1 (the `Except (Vec n α)` carrier collapses an
element-lazy error — **verified**: SAW `7` vs `9`, Lean proves them
equal with allowlisted axioms), F-2 (`mkFloat`/`mkDouble` share a
Lean body; this is SEAMS-D3 from audit 1, now settled affirmative),
LIB-2 (uninterpreted-in-SAW primitives given Lean values — the
weaker-statement flavour of the same collapse).

**Closure:** the invariant is *every translation function appearing
on both sides of an emitted equation must be injective on the
SAW-distinguishable domain.* The domain is finite and enumerable: the
`SpecialTreatment`/`mapsTo` table, the carrier adaptations in
`Convention.hs`, and the uninterpreted-primitive list. Each entry
needs an injectivity argument **or** an emission-time refusal. This
is the single most valuable *translator-side* audit remaining, and
unlike C1–C4 it is real work rather than a scripted check.

**This category is the one a perfect trust kernel cannot help with.**

### C6 — Obligation that does not constrain the value — CLOSEABLE, checkable invariant

*A contract takes a proof argument that the realization's value does
not depend on, so the obligation can be dropped without changing the
term.*

Instances: S-1(a) (`saw_stream_realize` ignores `mkfn` and `_h`),
S-1(b) (`Classical.choice` takes a Prop ⇒ proof-irrelevant ⇒
erasable). Immune by construction: `saw_mkStream_choose` and
`saw_fix_choose_raw`, which use `Classical.choose` — the predicate
rides as a type-level implicit.

**Closure:** a library-wide invariant with a mechanical test — *for
every `saw_*` realization taking an obligation `h : P`, the emitted
value must not be defeq to a term that does not mention `h`.* The
discriminator is already crisp (`choice` = erasable, `choose` =
binding), so the audit is: walk every realization, classify, and fix
or gate the erasable ones. Two are known bad; the rest have never
been checked as a class.

### C7 — Text proxy for an environment property — the subject of this plan

Instances: A-1, A-5, A-6, A-7, A-10, plus the goal-presence half of
R-1/A-2. Closure: §4–§5 below. Note C7 is *not* the largest category
— C1 and C5 each cost more — but it is the one whose closure is
already designed.

### Priority given the threat model

C1, C2, C3, C4 are cheap, mechanical, and each closes a whole class:
**do them first**, before the individual A-findings. C6 is a
focused library sweep. C7 is this plan. C5 is the long pole and the
only one that needs translator work.

## 4. The mechanism

The checker already compiles the user's file to `UserProof.olean`
and runs probe modules that import it. Those probes can query the
*environment* instead of the text. Four questions replace six greps:

| Question | Replaces | Closes |
|---|---|---|
| **What did this module declare?** — the constants `UserProof` adds beyond its imports | the `theorem\|lemma` closer awk | A-5 (`def hidden` is in the added set regardless of keyword) |
| **What does it depend on?** — `#print axioms` over *every* added declaration | the `sorry` text scans | A-10 (the real question was always `sorryAx`, never the token) |
| **Does it prove the goal?** — a real `theorem __replay_binding : goal := goal_closed` added to the environment | `#check (goal_closed : goal)` | the elaborator-only binding (kernel-checked instead) |
| **Did it extend the environment?** — added parser extensions, attributes, instances are enumerable | the lint's approximation of the same | A-1, A-7 (and the *general* case, not the listed tokens) |

The structural point behind all four (RK-9): **`#check` adds no
declaration and is therefore never kernel-checked.** Every gate
binding user content to the authority — binding, drift, triviality —
is currently a `#check`, so each verdict rests on the elaborator
alone, in an environment the user's module extends (token table,
instances, coercions). Converting these to declarations moves them
under the kernel.

### The honest exception, argued in place

One class genuinely **cannot** be checked from inside Lean
afterwards: **options that change how the module was built.**
`debug.skipKernelTC` (A-6) means the declarations in
`UserProof.olean` were never kernel-checked when added, and importing
a module does not re-check it — so a downstream environment query
inherits the damage. For that class the answer is not a better grep
either: it is to **stop the user controlling the build** (the checker
invokes Lean, so it can pass the options it wants and refuse a file
that sets any). The source lint remains as a **named backstop for
this narrow case only** — not as the primary mechanism for the other
five rows.

A second, smaller exception: the property "this file does not
*attempt* something forbidden" is genuinely about source text when we
want to reject *before* elaboration for defence-in-depth. Keeping a
lint for that is legitimate; claiming it is the guarantee is not.

---

## 5. Staged migration

Each stage is independently landable and independently pinned. Stages
S0–S1 are the release-blocking ones.

### S0 — Stop the bleeding (syntactic, deliberately)

The one-line hardenings that buy time while the real work lands.
These are *not* the plan; they are triage, and each must be labelled
as a backstop in the code so it is not mistaken for the guarantee.

- `gsub(/[«»]/, "", out)` before the lint denylist match (A-6).
- Add the syntax-declaring commands to the denylist (A-1's other
  half — **required**, per the verification above).
- Accumulate `out` across attribute brackets (A-7).
- `has_goal_def == 0` ⇒ hard fail on the plain path too (A-2), and
  RK-7's `awk` exit check.

### S1 — The kernel-checked binding (closes A-5, the T2 finding)

Replace `#check (goal_closed : goal)` with

```lean
theorem __replay_binding : goal := goal_closed
#print axioms __replay_binding
```

audited under the existing allowlist. This is the single
highest-value change in the plan: it makes the binding a *kernel*
obligation and routes it through the axiom audit, so a coercion to a
hidden `native_decide` proof is caught by name.

**Caveat, verified:** this does **not** close A-1 on its own. Land it
together with S0's lint additions.

### S2 — Declaration enumeration (closes A-5's root, subsumes the awk)

Emit a probe that enumerates the constants `UserProof` adds beyond
its imports, and audit **all** of them, not the ones matching
`^theorem|lemma`. Mechanism: compare the environment before/after the
import in a `CommandElabM` probe, or `Lean.Environment.constants`
filtered by module index. Then the closer set is a *fact* rather than
a parse.

Consequence: the "named closer" rule can be stated properly — *every*
declaration the user's module adds is audited; none can hide behind a
keyword the awk does not match.

### S3 — Environment-extension enumeration (closes A-1's root)

Enumerate added parser extensions / attributes / instances rather
than banning tokens. This is what the lint approximates, and it is
the difference between "we listed the escapes we thought of" and "we
enumerated what the module did." Investigate cost: this is the
stage most likely to hit Lean-API friction, and it is the one where a
*loud refusal on anything we cannot enumerate* is the honest fallback.

### S4 — Controlled build (closes A-6's root)

The checker passes its own options and refuses a user file that sets
build-affecting options, so the kernel cannot be switched off for the
module. With S4 in place, the lint's role shrinks to defence in
depth and can be labelled as such truthfully.

### Drift and triviality probes

Same treatment (RK-9), lower priority: both are `#check`s today.
Drift additionally needs the S-1 fix below, which is a *contract*
change, not a checker change.

---

## 6. What this plan does NOT fix

Stating this plainly matters more than the plan itself — a semantic
kernel that is *believed* to cover these would be worse than the
current honest one.

- **S-1 (erasable obligations)** is not a checker defect. No gate can
  detect a missing obligation when the emitted *value* is defeq
  without it — verified above with two `rfl`s. The fix is in the
  **contract**: route the value through `Classical.choose` of an
  existential (as `saw_mkStream_choose` already does, making the
  obligation a type-level implicit and therefore binding), and/or
  require every authority `h_*obligation_` line to appear in the
  completed outline with a present, non-`sorry` binder. FIX-SEAM ⇒
  pause rule applies.
- **S-2 (raw fix contract)** is not fixable by any checker: the
  contract is extensional and cannot observe SAW's operational
  divergence. Every check goes green *honestly*. Only a
  productivity-gated contract or an emitter-side refusal closes it.
- **LIB-1 (wrapped-vector carrier)** is a *translator* defect and the
  most serious non-gate finding: verified above that a SAW-false
  equation proves in Lean using only allowlisted axioms. A perfect
  trust kernel admits it, because the Lean statement really is
  proved — it is the wrong statement. Fix is in the carrier or in an
  emission-time refusal.
- **F-5 (`sort 0 → Type` narrowing)** — same character: the emitted
  goal is *weaker* than the SAW obligation, and the kernel's job is
  not to notice that.
- **T3 threats** — unchanged by anything here, by design.

The honest summary: **the semantic kernel closes the "gate can be
satisfied without proving the obligation" class. It does nothing for
the "we emitted the wrong obligation" class**, which is the
translator's problem and is where LIB-1, F-5, S-2 and the fragment
semantics programme live.

---

## 7. Gates

- Every stage lands with a red-before/green-after row under
  `saw-boundary/` (or a `trust-tier-selftest.sh` case for
  checker-internal rules), per the standing rule that every guard
  ships with a mutation it demonstrably catches.
- The A-1/A-2/A-5 witnesses in §2 become permanent rows; they are
  currently reproduced by hand.
- RK-5 must land alongside S1–S2 or the CI harness cannot catch
  regressions of either (it binds inside the user's own module
  today).
- `2026-05-02_residual-trust.md` gains the T3 paragraph — the
  dev-override affordances are currently undocumented trust.
