# Trust-kernel design review — deletion-biased (2026-07-31)

Charge (user): substantial danger of building checker/trust-kernel
cruft back up through the fix-audit process; want a clean design
rather than something fancy that is itself a source of bugs; cut
surrounding infra while keeping things honest; highlight cleanly
where things built back up since the D2 cut.

Method: kernel read end-to-end at `1cb4bdffb`; re-accretion
measured against the D2-cut baseline (`6c3557cdc`); every check
classified; proposals drafted and then put through an ADVERSARIAL
design review (opus, refute-by-default, empirical probes) BEFORE
reaching the user. That review REFUTED the first draft's central
proposal with an end-to-end demonstration — the draft would have
re-opened the very hole three audit rounds closed — and this
version is rewritten around what survived. The refutation is
itself the review's strongest lesson (§4).

## 1. Re-accretion since the D2 cut — measured

(Counting rules: CODE = non-comment, non-blank lines; tokens =
unique `fail "…"` strings; cases = `expect_fail`+`expect_ok`
invocations / `lint_case` rows. Adversarially re-derived; two
base counts in the first draft were off by 1–2 under a different
counting rule, deltas confirmed exact.)

| file | D2 cut | now | delta |
|---|---|---|---|
| `lean-check-core.sh` (total) | 532 | 613 | **+81** |
| `lean-check-core.sh` (CODE) | 216 | 232 | **+16** |
| `proof-source-lint.awk` (total / CODE) | 186 / 90 | 235 / 92 | **+49 / +2** |
| `replay-kernel-selftest.sh` | 663 | 784 | **+121** |
| `trust-tier-selftest.sh` | 365 | 390 | **+25** |
| kernel fail tokens (unique) | 29 | 32 | **+3** |
| kernel selftest cases | 19 | 24 | **+5** |
| lint unit cases | 8 | 11 | **+3** |

Honest reading: kernel CODE grew only +16 lines — but they are the
wrong sixteen, and ~240 lines of comments and tests exist to
explain and pin them. Two concentration points:

1. **The triviality gate**: 3-line probe → probe + rc branch +
   refutation-message ALLOWLIST + give-up DENYLIST + ~40 comment
   lines + 2 cases + one waiver added-then-deleted, through THREE
   same-day audit rounds each refuting the previous discriminator.
   The accept condition is coupled to Lean's error phrasing on one
   toolchain version.
2. **The lint exit-code split**: a truthful-diagnostics fix that
   grew an exit-code contract, axiom-first precedence with a
   per-line caveat, and +3 fixtures — for a distinction between
   two paths that both reject.

The observation layer (ship-list, data-mode, pins) also grew;
that growth is derivation replacing hand lists, fails toward
false-red, sits outside the trust boundary, and is NOT cruft.
It is explicitly out of scope for cutting.

## 2. Check inventory — classification

**[K]** ask-the-kernel; **[M]** mechanical (digests, existence,
exit codes — no content discrimination); **[T]** text
discrimination (the rot-prone class).

| token(s) | class | verdict |
|---|---|---|
| absolute-path/existence/env guards (project-root-not-absolute, stage-dir-not-absolute, missing-emitted/proof, cannot-create-work-stage, stage-copy-failed, no-digest-guard, no-timeout-guard, support-library-build) | [M] | KEEP |
| user-file-{deleted,mutated}-mid-check, completed-path-emitted-not-linted | [M] | KEEP (D3/D4 core) |
| sorry-in-user-file, unsanctioned-sorry-in-emitted | [T] | KEEP — single greps, sorryAx-audit backstop (verified: allowlist is exactly propext/Classical.choice/Quot.sound) |
| axiom-decl-in-user-file + proof-source-unlintable + awk | [T] | KEEP AS-IS for 0.02; collapse DEFERRED to 0.03 (§3.2) |
| goal-presence family | [T] | KEEP — C1 invariant; F12 positive-classifier successor filed for 0.03 |
| harness-namespace-in-user-file | [T] | KEEP — one grep |
| goal-formation-trivial + triviality-probe-inconclusive | [K] question, [T] decoder | **USER DECISION — §3.1** |
| compile/elaboration gates; `__drift_binding`; `__replay_binding` family; axiom-audit trio | [K] | KEEP UNCHANGED |

## 3. Proposals (as amended by the adversarial review)

### 3.1 The triviality gate — a genuine A/B decision, not a free deletion

The first draft proposed replacing the allowlist+denylist with a
control probe + generous limits + "no inspection of why". The
adversarial review REFUTED it end-to-end: it staged
`goal := (List.replicate 100000 true).length = 1000000-shape` —
the wave-5 demonstration scaled up, semantically trivial (`rfl`
closes it at depth 1e6 in 10.9s), an in-model backend-error shape
— and showed the current kernel fails it CLOSED
(`triviality-probe-inconclusive`) while the drafted design ADMITS
it (`CHECK-OK`, zero axioms, binding green). The structural fact
under the demonstration: **no [K] check catches goal-formation
defects** — the binding honestly binds the destroyed goal, the
drift check compares two outputs of the same emitter, the audit
sees a clean `rfl`. This gate is the ONLY defense in its class,
and its "unrecognized" outcome must default to reject. The review
also showed the draft re-opened the CP-3 timeout fail-open
(rc=124 → proceed, demonstrated), rested the control probe on a
false premise (on the completed path `Emitted` IS user-authored
bytes), and would have deleted the token's only live pin. Full
enumeration: of eight probe-outcome classes, the draft was WORSE
(reject→proceed) in six, identical in one, better in one — and
the one improvement was availability-only against a hypothetical
future toolchain phrasing.

So the honest menu is:

**Option A — harden in place (the reviewer's amended design;
CODE-neutral, not smaller):** keep the allowlist (it is what makes
"unrecognized" fail closed); ADD a mechanical rc-class guard
(rc ∈ {124,137,139} or empty transcript → inconclusive — [M], and
it closes the timeout class independently of any regex); ADD the
control probe, run FIRST, with an honest rationale (not
env-class); raise the probe limits ONLY after a corpus
measurement (raising limits makes strictly more rows trivially
closable — an unmeasured fail-closed corpus risk); keep the
denylist unless a fresh probe shows generous limits close the
laundering channels; add a deep regression row (n=100000) so the
inconclusive token keeps a live pin. Net: the gate becomes MORE
correct, roughly the same size. This is the conservative choice;
it accepts that this particular check cannot shrink in the
drafted direction.

**Option B — delete the gate outright (the real deletion):** the
threat model's own load-bearing list (consequence 2) names three
checks — the binding, the audit, the drift check — and the
triviality gate is not among them. Delete both tokens, both
regexes, the probe, and its three selftest cases (~50 kernel
lines, −2 tokens, −3 cases); record the residual honestly in
residual-trust.md: *a trivialized emission whose trivial goal the
user (or their automation) discharges without noticing is
admitted; the defenses are the differential/conformance corpus
catching emitter trivialization at development time, and the fact
that an honest user reading Emitted.lean sees a goal that says
`True`.* The gate's three audit rounds in one day are the
empirical case that this check cannot be kept "small enough to be
kept honest" (the threat model's own condition for courtesy
checks). The cost: replay-time defense-in-depth for NOVEL user
goals — the one place the corpus cannot reach — is gone.

**Recommendation: Option B**, by the project's own precedent. D2
faced exactly this structure — a text mechanism whose fix-defect
rate exceeded the risk it retired — and resolved it by scope
reduction plus honest documentation, not by hardening. Every
subsequent audit validated that call. The residual B accepts is
in-model but requires a conjunction (emitter trivialization bug
AND an unnoticed rubber-stamp discharge of a visibly-trivial
goal) and is documented rather than silently absent. Option A is
defensible if that conjunction is judged too cheap; it should
then be implemented exactly as the amended design above, with its
three blocking empirical checks (regression pin first, corpus
sweep before limits change, laundering re-probe before any
denylist cut).

### 3.2 Lint token collapse — DEFERRED to 0.03

The adversarial review confirmed the split is diagnostic-only (no
consumer branches on any token — verified across all .hs and the
harnesses) so the collapse is SAFE — but the first draft's blast
radius missed the mirrored implementation in
`lean-proof-test.sh` (collapsing only the kernel would create a
gate-path divergence, the exact class wave 5's clause-2 list
names), two .saw comment sites, and the awk-crash case where the
token NAME is currently the only signal. Five goldens/sources,
four expectations, two fixtures, six doc sites, two lockstep
implementations — on landed, swept work, for a diagnostics
nicety. The churn rule this review exists to enforce says no.
Fold into 0.03 alongside the F12 lint successor.

### 3.3 The standing rule (contributing.md, beside C1–C6) — amended

The first draft's wording ("never by a smarter regex") would have
FORBIDDEN the CP-3 allowlist fix — the very mechanism currently
holding four in-model fail-open classes closed. Adopted wording:

> Fix-audit responses to courtesy-layer findings are resolved by
> deletion, by conversion to a kernel question, by documentation,
> or by making the mechanism's UNRECOGNIZED case fail closed. No
> fix may change any outcome class's default from reject to
> proceed; a change that does is a soundness change and requires
> its own audit, not a deletion audit. Prefer mechanical
> discriminators (exit codes, digests, existence) over text ones;
> a new text discriminator in the trust kernel requires a written
> argument that no mechanical one exists.

### 3.4 Reserve disposition

Plan 3b (retire `native-eval`) stays IN RESERVE for 0.03 — corpus
churn, not kernel cruft. Recorded as a decision, not a leftover.

## 4. What the review process itself showed

The first draft of this document — written under an explicit
deletion bias, by the same process that produced the accretion —
proposed a simplification that was demonstrably unsound, with the
soundness hole hidden under a plausible-sounding sentence
("never an admission of anything the [K] core would refuse" —
vacuously true, materially false). The adversarial pass caught it
before implementation, with a staged end-to-end admission. Two
morals, both now encoded in §3.3's rule: deletion bias needs the
same adversarial discipline as accretion; and the classification
that PREVENTS this mistake is to name each check's QUESTION and
its DECODER separately — the triviality gate asks a [K] question
and the cruft is in the decoder, so "simplify the decoder" must
never quietly become "ignore the answer".

## 5. End state (honest arithmetic)

Under Option B + deferrals: kernel CODE ≈ 232 → ~185 (below the
D2 baseline of 216), tokens 32 → 30, kernel cases 24 → 21, both
regexes gone, zero text coupling to tool output anywhere in the
trust path — with the residual documented, the rule of §3.3 in
force, and the [K]+[M] core byte-unchanged. Under Option A:
CODE-neutral, tokens unchanged, correctness improved; the first
draft's "back at-or-below D2 baseline" claim is unreachable and
withdrawn. Either way: one sweep + one focused audit of the
change, then the release decisions.
