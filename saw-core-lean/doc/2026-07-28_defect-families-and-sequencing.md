# Defect families, convergence, and pre-release sequencing (2026-07-28)

Written at the pre-audit decision point, in answer to a direct
question: are the accumulating emission fixes whack-a-mole, and do we
need an *audit* or a *plan*? Answer: **three families, two of which
already have named roots and plans; the third has neither, and it is
the one still producing findings. We need a PLAN for that family
first, then the audit.** Rationale and sequencing below.

## The three families

Every finding from `2026-07-24_soundness-audit.md`,
`2026-07-24_soundness-audit-2.md`, and the 2026-07-25→28 close-out
sorts into one of three roots. This is not a taxonomy for its own
sake: two of the roots are already named, and knowing which family a
new finding belongs to tells you whether to fix the instance or wait
for the programme.

### Family 1 — the trust kernel asks text questions about a semantic object

A-1 (notation capture), A-2 (goal-def regex), A-5 (`#check`
coercion), A-6 (escaped name components), A-7 (multi-line
attributes), R-1 (completed-outline binding), A-10 (contradictory
`sorry` rules), RK-5 (harness bound in the user's scope), RK-7 (awk
hard-error read as clean).

These are one defect enumerated: properties of an *elaborated Lean
environment* established by pattern-matching *source text*. The
individual fixes were genuine mole-whacks — and the project noticed,
which is what A-11 records.

**Root: NAMED. Plan of record:
`doc/2026-07-24_semantic-trust-kernel-plan.md`.** Lean can answer
five of the six kernel questions authoritatively; the checker is
already positioned to ask.

### Family 2 — the translation has no model of SAW's partiality

LIB-1 (errors: lazy element-wise vs eager whole-value carrier), S-2
(divergence: an extensional fixed-point contract cannot observe ⊥),
S-1 (obligations erasable because nothing tied them to anything
operational), and the `divNat`/`IntMod` boundary questions (F-3,
LIB-3, F1).

SAW is lazy, element-wise, and has genuine ⊥. `Except String T` is
eager and whole-value, and an extensional Lean statement cannot see
non-termination. Errors and divergence are the two faces of one
missing model.

**Root: NAMED. Plan of record:
`doc/2026-07-16_fragment-semantics-scoping.md` (Phase A pointwise-lazy
adequacy model), with LIB-1's carrier remedy (a) as its
value-domain instance and the productivity-gated raw fix contract as
its recursion instance.** Deferred to 0.03 deliberately, and LIB-1
is shipped documented under that deferral (user decision 2026-07-28;
`README.md`, residual-trust §3.2e).

### Family 3 — emission conventions (THE OPEN ONE)

F-8 (binder annotation taken from the lambda while the type came
from the Pi), F-1 (definition annotated raw for a wrapped-domain
body), A-4 (`Prec` ignored for sorts), F-6/F-7 (emitted name
collisions), F-2 core (recursor head emitted short, its ctor-order
assertion qualified).

Five findings, one area, and — unlike the other two families — **no
unifying account and no plan.** That is why this family keeps
producing findings and why the fixes feel like whack-a-mole: they
are, because nobody has stated what would make them stop.

**Proposed root.** The position/callee calculus made *adaptation*
safe: a single chokepoint (`adaptTo`) where forbidden adaptations are
unrepresentable. That worked, and it is why LIB-1 is a
representational defect rather than an adaptation slip, and why
nothing downstream can silently absorb F-1's stray `Except`.

It left *annotation* unguarded. The type an emitted definition
DECLARES is computed by a different path from the one that builds
its BODY, and the vocabulary that path consults
(`BindingRaw`/`BindingWrapped`/`BindingFunction`) is coarser than the
invariant it must enforce — `BindingFunction` records nothing about
the formals' representation, which is exactly F-1. F-8 was the same
shape, and its own code comment admitted the two translations could
disagree.

> **The missing invariant: the emitted signature must be derived from
> the same authority as the emitted body.** Annotation needs the
> structural counterpart to `adaptTo` — a chokepoint where a
> signature that does not match the body it introduces cannot be
> expressed.

F-8 was fixed exactly this way (take the PI's binder type; the
declared type IS the authority) — but as a local fix, not as a
stated rule, so F-1 was still reachable in a different emitter.

## Are we converging?

**Yes on Families 1 and 2, not yet on Family 3.** Evidence, so a
future reader can re-judge rather than take this on trust:

Converging:
- **Severity falls monotonically.** Audit 1: one CRITICAL (replay
  hole). Audit 2: three CRITICALs. 2026-07-28 close-out: a dead
  flag, a stale claim, an over-approximation.
- **Today's pass produced almost no new defects.** Working the
  entire owed-pins ledger, the docs batch and F-1 turned up mostly
  STALE BOOKKEEPING: pins that already existed (RK-5's decoy case,
  the A-6/A-7 lint cases, the A-5 kernel-selftest vector), claims
  already corrected, and — in F-1's case — an audit premise that had
  become FALSE because the code improved underneath it
  (`cryptol_rev_module` is now the compiling witness the audit said
  did not exist). A system that reports "your notes are out of date"
  rather than "here is another hole" is converging.
- **By-construction is the reflex.** F-8's refusal gate was DELETED
  in favour of taking the Pi type; S-1 routes through
  `Classical.choose` so the obligation cannot be erased; F-7 refuses
  rather than renames; `lowerFixProofObligation` was deleted, not
  bypassed.
- **Class-catching mechanisms are landing**, and they fire on their
  authors: `doc-claim-lint.sh` caught this session citing a lemma
  (`genWithBoundsM_ok_of_total`) that does not exist yet — precisely
  its A-3 job.

Not converged / warning signs:
- **Interim fixes are stacking and they interact.** S-1 is
  explicitly interim (strategy A, revert when C lands); LIB-1 is
  documented-not-fixed; S-3's second half deferred. The
  (b-evidence) scrutiny hit the interaction directly: S-1's interim
  weakens the "the obligation is the backstop" argument that S-3's
  disposition leans on.
- **`Term.hs` is ~5,500 lines and the split has not happened**,
  though TODO.md says do it BEFORE the audit so reviewers see the
  final structure. Family 3 lives in that file.
- **The finding rate is not zero**: the S-3 analysis found a new
  recognizer hole the sixth audit missed (a permuting wrapper ABOVE
  the zip, mirror of the one below it that Finding 0 closed).

## Audit or plan?

**Both, in this order: plan for Family 3, then audit.**

An audit is for finding what we do NOT know. We already know Family
3's instances; what is missing is an account of why they stop. Auditing
first spends reviewer lanes rediscovering F-1-class issues in code we
are about to restructure — and the audit charter's own working
assumption ("a defect exists until the surface is shown sound") is
much harder to satisfy for a surface with no stated invariant.

Conversely we should NOT skip the audit once the plan lands: Families
1 and 2 are deferred by decision, not closed, and the panel's job
includes checking that those dispositions are honest and that no
FOURTH family exists. The audit is the release gate; this only
sequences it.

## Sequencing (plan of record from 2026-07-28)

1. **S-3 narrowing** — landed same day; low-risk, strictly narrowing,
   independently valuable (see TODO).
2. **Family 3 plan + execution**, as ONE pass, not three drive-bys:
   - the `Term.hs` split (already required pre-audit);
   - a design note stating the annotation invariant above and where
     its chokepoint lives;
   - the three open emission items folded in as instances rather
     than fixed individually: F-1's top-level annotation, F-2 core's
     recursor-head qualification (a naming-convention decision that
     changes what a USER writes in a discharge — 15 rows, four
     hand-written artifacts, so it needs the pass's framing to be
     coherent), and the unused-Pi-binder printer cosmetic.
3. **Pre-release soundness review** (the multi-reviewer panel) —
   against the restructured, invariant-stated emitter.
4. **0.03 programme**, unchanged in content, now with a stated
   family mapping: fragment semantics (Family 2) with LIB-1's
   carrier remedy and the productivity-gated raw fix contract; the
   semantic trust kernel (Family 1); the recognizer extension behind
   Phase A.

The speculative work (Families 1 and 2) stays after the audit
deliberately: both are large, both are already dispositioned in
writing, and neither blocks the gate now that LIB-1 ships documented.
