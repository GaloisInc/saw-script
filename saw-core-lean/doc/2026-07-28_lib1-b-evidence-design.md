# LIB-1 interim option (b-evidence): design scrutiny (2026-07-28)

Requested deliverable: a careful design note on (b-evidence) — admit
a throw-capable element when its throw sources carry discharged
evidence — written to SHAKE OUT bugs before any implementation.
Verdict up front: **the scrutiny found five structural defects, one
of them foundational; (b-evidence) as recorded in TODO.md dissolves
under it.** What survives is a different (larger) design,
(b-totality), whose honest cost/benefit loses to accelerating (a).
The defects are recorded first — they are the durable content.

Companion measurement: `doc/2026-07-28_lib1-scope-measurement.md`
(59 of 350 artifacts have a thrower inside an element position; 57
via `atRuntimeCheckedM`).

## The claim under scrutiny

> An element body that can throw is admitted when its only throw
> sources are checked operations whose obligations are discharged
> in-artifact — a discharged bounds proof makes the throw branch
> dead, the element provably `Except.ok`, and the collapse
> unobservable.

The soundness core is right, and worth stating precisely because it
is the part worth keeping (§ "The salvageable lemma" below). The
defects are in everything around it.

## B1 (foundational): the evidence the design relies on does not exist

`atRuntimeCheckedM`'s own docstring: it is the realization for index
positions "whose bound is NOT derivable at the emission site"
(OP-2). The translator ALREADY splits on evidence: derivable bounds
emit `atWithProof_checkedM … (h : i < n)` — total given `h`, no
throw, and NOT a LIB-1 hazard at all; only underivable bounds emit
the throwing runtime-checked form. So for the 57 dominant artifacts
there IS no in-artifact obligation to point at — **the throw is live
precisely because evidence was unavailable.** "Admit when the
obligation is discharged" is vacuous over the set it was designed to
save: every element that HAS discharged evidence is already
non-throwing, and every element the gate must judge has none.

Consequence: (b-evidence) can only be realized by MINTING new
evidence — a per-element totality obligation
(`∀ i (h : i < n), ∃ v, elem i h = Except.ok v`), emitted into the
artifact and required to discharge. That is a different design —
call it (b-totality) — and the remaining defects apply to it.

## B2: the gate fires at the wrong time, violating the S-3 discipline

A totality obligation discharges (or fails) at Lean elaboration, not
at translation. An element whose totality the canned tactic cannot
close would surface as a check-time tactic failure inside a
generated artifact — exactly the pattern S-3 condemns ("converts an
intended emission-time named rejection into a check-time
undischargeable obligation," violating reject-when-unsure). The
translator cannot run Lean at translation time, so this is not
fixable by moving the check: (b-totality) STRUCTURALLY cannot give
the named-diagnostic-at-translation behavior every other boundary in
this backend has. At best the translator names the construct and the
artifact carries the failure — a two-place diagnostic no other
rejection has.

## B3: the syntactic scan must be reference-closed — demonstrated

A thrower need not appear inside the element span: the emitter
let-shares subterms (`let x__ … := RHS;`), and a throwing RHS
referenced from inside an element is semantically in-element.
**Live witness: `differential/vector_literal_edges/observed.lean`**
— a let-bound thrower referenced inside both `genWithBoundsM` and
`vecSequenceM` element spans (found by the reference-closure check
this note forced; the span-only census undercounts, e.g.
`vecSequenceM` is 2 by span, ≥3 closed). Worse, closure is
INTERPROCEDURAL: module translation (`write_lean_cryptol_module`)
emits elements that call module-local definitions
(`cryptol_module_simple`, `cryptol_module_popcount` are in the 57),
so "can this element throw" must traverse the translated module's
call graph. That is an effect system for the emitted fragment — new
delicate analysis in a trust path.

## B4: guard-awareness, or the analysis over-rejects the safe idiom

`iteM` discards the unselected branch (audit-verified NOT affected —
the branch analogue of this bug, handled correctly). A thrower under
a guard that excludes it at runtime is dead; a guard-blind syntactic
scan rejects it anyway, and the guarded-read idiom (`iteM (i < k)
(at …) default`) is exactly how real elements defend indexing. So
either the scan reasons about guards (more analysis), or the
totality obligation does — and the emitted canned tactic
(`assumption | omega | simp …; omega`) cannot case-split monadic
`iteM` guards today. New tactic machinery, in the evidence chain,
with the F-1 lesson standing (an "audited safe" claim about an
untested path was itself the defect).

## B5: dischargeability on the target rows is unproven, with a known
hostile subset

OP-2's implementation record names the two surfaces that stayed
sorry-pinned: guard-dependent `iteM` branch bounds and
value-dependent bounds over runtime Nats. Those are element-position
bounds the interval analysis could not entail — the same population
(b-totality) must now discharge with a canned tactic. Favorable
evidence exists: every currently-DISCHARGED row de facto proves its
elements total (a thrown element would falsify its `… = ok …` goal),
so totality is TRUE for that corpus; but true-and-canned-provable is
the F-4-shaped gap, and the 91 obligation-shape rows that emit
without discharging would each grow a new must-close lemma. Nobody
can size the failure set without building the machinery — the
LIB-2 precedent ("the estimate was wrong twice, in both directions")
applies squarely.

## B6: precedent — this is the shape of machinery this project deletes

F-8's refusal gate was built and DELETED when structural comparison
false-positived on legitimate rows; the recorded lesson was "make it
unreachable by construction instead of detecting it." S-1's interim
fix was accepted only with a by-construction successor named. The
by-construction fix here is (a): `Vec n (Except String T')` cannot
represent the collapse, so there is nothing to detect, no effect
system, no tactic-power question, no two-place diagnostics.
(b-totality) builds a large fraction of (a)'s reasoning burden
(per-element ok-ness, everywhere) while KEEPING the unfaithful
carrier it reasons about.

## The salvageable lemma (keep this even if nothing else survives)

The soundness core, stated so it can be kernel-checked ONCE in the
library rather than trusted per artifact:

> If `∀ i (h : i < n), ∃ v, f i h = Except.ok v`, then
> `genWithBoundsM n α f = Except.ok (Vector.ofFn (fun i => choose …))`
> — and consequently any statement over the collapsed carrier value
> coincides with the statement over the faithful per-element carrier.
> (Induction on `Vector.ofFnM`'s sequencing; the collapse is
> observable only through an erring element.) Same shape for
> `vecSequenceM` literals (finite conjunction of element totality).

Any future gate — and (a)'s migration proofs — should rest on this
lemma family (`genWithBoundsM_ok_of_total`, `vecSequenceM_ok_of_all_ok`),
not on a translator-side claim. This also aligns with A-11's
plan-of-record: totality is a question Lean can answer
authoritatively; awk cannot.

Deliberately NOT leaned on anywhere above: the "divergence also
needs a partial downstream observer" refinement. Observers can be
embedded anywhere in an equation under binders; no gate can locate
them, so no admission decision may depend on their absence.

## Recommendation

1. **Do not build (b-evidence)/(b-totality).** B1 voids the recorded
   design; B2–B5 price the salvage at (a)-scale effort with a worse
   endpoint; B6 says we would likely delete it.
2. **Short term (release-gate honesty):** (b-narrow) — reject
   elements that can reach `saw_throw_error` or the runtime
   division/ratio family, REFERENCE-CLOSED (B3's witness makes
   span-local scanning insufficient even at narrow scope). Measured
   cost ~2 rows. Plus a residual-trust entry stating plainly that
   the `atRuntimeCheckedM`-element half of LIB-1 remains OPEN and is
   closed only by (a).
3. **Fix: accelerate (a)** — the faithful carrier, scoped as its own
   design doc, building on the salvageable lemma family and the
   position-calculus adaptation chokepoint (`adaptTo`), which is the
   architecture's intended place for exactly this kind of
   representation change.

User decision points: accept (b-narrow)'s honestly-partial interim
(vs. no interim at all), and whether (a) enters 0.03 at the front of
the queue or preempts it.
