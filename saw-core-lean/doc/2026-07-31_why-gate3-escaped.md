# Why the gate-3 escape survived three audit waves (2026-07-31)

Written because the close-out plan's §5 failure clause fired: a
CRITICAL surfaced in a previously-audited surface, and the clause
requires reassessing the convergence diagnosis in a doc *before*
the finding is treated as routine. The defect itself is recorded at
`Signature.hs` limit 2 and pinned by
`saw-boundary/goal_except_carried_binder_refusal/except_carried_named_hypothesis`.

## The defect in one paragraph

Gate 3 (the W2-UNRUN-1 fix, landed 2026-07-30) refuses a goal whose
telescope folds a sequent hypothesis whose Lean image is an equation
over the `Except String` carrier — such an image can be UNINHABITED,
making the emitted implication vacuously provable while the SAW
obligation is false. Its TEST 1 exempted every NAMED binder, on the
premise that "a named domain is never a folded hypothesis". Naming
the binder — `(h : EqTrue …) -> …`, hand-written through
`parse_core`/`prove_core`, both Current builtins — walked the same
goal straight past the gate. Measured before the fix: SAW proves the
hypothesis and refutes the conclusion (obligation FALSE), the
emitted goal proves in Lean with `[propext, Quot.sound]` (both
ALLOWLISTED), so replay would have issued `LeanReplayEvidence` for a
false claim. The anonymous spelling of the identical goal was
refused — which is precisely what kept the hole invisible.

## Why it happened — the causal chain

**1. The limit was known and written down.** It is literally
"KNOWN LIMIT 2" in the gate's own comment, filed the day the gate
landed. This was not an unconsidered case.

**2. It was then "narrowed" by a measurement that answered a
different question than the claim it was cited for.** The
2026-07-30 narrowing ran a real command with a real result: `parse_core
"Except"` fails with `Unbound name: Except`, so a user cannot
hand-write a binder that *mentions the carrier*. True, and still
true. But the escape never required the user to mention the
carrier — the comment says so itself in the very next clause
("Every carrier mention in a goal is introduced by this
translator's own value wrapping") and then draws the opposite
conclusion, resting on a second clause that was **never measured**:
"the wrapping names a binder only when the SAWCore Pi it images is
dependent". That is false — the Lean binder name is copied from the
SAWCore `VarName` regardless of dependency. One clause measured,
one clause assumed, one conclusion drawn as if both were measured.

**3. The measurement made things WORSE than no measurement.** A
question that was open became, in the written record, closed. Every
later reader — including me, three sessions on — saw "Measured
narrower than it first looks (2026-07-30)" with a command and a
result, and moved on. Unmeasured assumptions are read as
conservative; *partially* measured ones are read as settled. This is
the mechanism worth internalizing: **a measurement's scope must be
stated relative to the claim it is being used to support**, or it
launders an assumption into an established fact.

**4. The ledger's own framing then sealed it.** The residual lived
as W2-UNRUN-2, whose text described the `FpOther` telescope
blindness — genuinely just coverage debt. Wave 3 marked it
"CONFIRMED-DEBT" without re-scoring. The item's label became a lid:
three subsequent waves read "debt" and allocated attention
elsewhere. The real defect was not in the item's text at all.

**5. No wave was pointed at the code.** Wave 4's docket was
FixRecognizer/demo/cabal/delta; wave 5's was CONFORMANCE/arc-delta/
residues. Neither read gate 3. It was audited once, on the day it
landed, by the process that wrote it.

**6. What finally found it** was the threat-model re-score you
asked for — because the charge said *read the code at HEAD, verify
the ledger's line numbers, and try to construct a remaining
in-model route*. The agent ignored the item's framing, went to the
source, and built the witness. The discipline worked; it was simply
pointed at this surface three days later than it should have been.

## What this does to the convergence diagnosis

The two-population diagnosis (translator = enumeration rot, cured
by derivation; kernel = text guards against an unstated adversarial
model, cured by scope reduction) is **not refuted, but it is
incomplete in a way that matters for release confidence.**

This defect belongs to neither population. It is EMISSION-side, and
the threat model already says that is where error lives ("Error
lives where meaning is constructed"). What it adds is the mechanism:
the emission-side goal-shape gates are guards whose logic rests on
**premises about the translator's own behavior** — where binder
names come from, what the printer does, which shapes `parse_core`
admits. Those premises are checkable in seconds and were instead
reasoned about. Both W2-UNRUN-1 and this escape are the same shape:
a gate that is correct about the route its author had in mind and
silent about a route its author asserted was impossible.

Note the symmetry with the kernel-side lesson from the same week.
The triviality gate's decoder was "fixed" three times by reasoning
about what Lean *prints*; each round was refuted by someone actually
running Lean. Gate 3's limit was "narrowed" by reasoning about what
a user can *write*; refuted by someone actually running SAW. **The
recurring root cause across both populations is reasoning about a
mechanism where exercising it was available and cheap.** That is a
third population — not of defects, but of how defects get
introduced — and it is the one the release process should now be
calibrated against.

## What follows (not a re-plan, a correction)

1. **Rule C8** (contributing.md, landing with the fix): a guard's
   stated limit may be narrowed only by a measurement whose scope
   is stated relative to the claim, and every clause of the
   narrowing argument must be independently checkable. Where a
   clause is an assumption, it must say so — and an assumption in a
   soundness argument is a pin obligation, not a comment.
2. **The emission-side gates get the next wave's docket.** Gate 3,
   the sort-binder gates, the telescope pin, `sequentToProp`'s
   contract — audited by lanes charged with constructing witnesses,
   not reading comments. This is a wave-6 charge, not a 0.02
   blocker beyond the fix landing here.
3. **W2-UNRUN-2's own residue** (the `FpOther` blindness) stands
   re-scored as LOW coverage debt and moves to 0.03 with a pin
   sketch — the re-score's finding, unchanged by any of the above.
4. **Release status**: this was release-blocking and is now fixed
   and pinned; clause 3 must be re-established at the new release
   commit. Nothing here reopens the kernel-side conclusions —
   wave 5 found no kernel defect and the design review shrank the
   kernel further.

## The honest summary

Three waves of audit, a design review, and a deletion pass all ran
over a codebase containing a demonstrable unsound-acceptance path,
and none of them found it, because it was hidden behind a comment
that said it had been checked. The finding is not evidence that the
audit process fails; it is evidence that **the audit process
inherits the trustworthiness of the written record it reasons
from** — and this project's written record is large, load-bearing,
and was until today one measurement short in one sentence.
