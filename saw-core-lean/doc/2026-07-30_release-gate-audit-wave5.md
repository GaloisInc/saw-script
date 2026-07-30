# Release gate — WAVE 5 verdict audit (2026-07-30, HEAD `237310fda`)

The verdict wave of the 0.02 close-out plan
(`2026-07-30_convergence-closeout-plan.md` step 4), judged against
that plan's §5 exit criterion, which was fixed in advance. Three
Opus docket lanes (CONFORMANCE.md semantic re-read; delta-composition
over all seventeen 2026-07-30 commits; residue adjudication),
adversarial verify on MEDIUM+, cross-finding consistency agent,
completeness critic as exit-criterion judge. 7 agents. 28 findings.

**VERDICT (the critic's, quoted in substance): DO NOT DECLARE THE
GATE MET AT `237310fda`.** Clauses 1 and 2 fail, clause 4 is
knowingly pending (CI deferred to merge), clause 3 holds
conditionally. Nothing found is release-blocking in the soundness
sense — zero CRITICALs, zero translator/kernel defects at MEDIUM+,
every involved surface fails closed — so this is a bookkeeping
shortfall, not a reopened soundness question. But §5 exists
precisely so a shortfall of this shape cannot be waved through by
the wave that found it. The honest reading: the gate is one small
commit plus one ledger pass away from met, not met.

## The one MEDIUM, and its class

**W5C-1 (MEDIUM, in-model, CONFIRMED by adversarial verify):**
CONFORMANCE.md's five `*WithProof` vector rows claim positive
`obligation` status and describe emitted checked bounds
obligations; at HEAD all five directories are `.known-gap`
REJECTION pins, because the contracts were removed 2026-07-25
(LIB-2) — giving those primitives Lean values made the emitted
statement strictly WEAKER than the SAW obligation. The file
declares itself "the live coverage matrix … this matrix is the
measure of coverage"; it advertises as covered a surface whose
coverage was withdrawn for unsoundness. Runtime is unaffected
(the surface rejects, fail-closed); the defect is entirely in the
evidence ledger — which this project treats as load-bearing.

**The class (critic GAP 1):** the same S-2/LIB-2 propagation
failure is live beyond CONFORMANCE.md — `architecture.md:189-191`,
`proof-cookbook.md:172-173`, `STATUS.md:290`,
`FixRecognizer.hs:17-19` Haddock, and the shipped
`SAWCorePrimitives.lean` docstrings for the `_raw` contracts
(W5C-7: the retired contracts' Lean definitions remain with
docstrings asserting they are emitted, and the obsolete-helper
denylist cannot match the `_raw` variants). `doc-claim-lint` is
structurally blind to all of it: it resolves identifiers by
textual containment (comments count), so it is green over false
claims in its own linted set. A third defect population, predicted
by neither half of the convergence diagnosis: **closed soundness
decisions do not propagate to the prose that cites them, and no
mechanism watches that propagation.**

**Calibration dispute, recorded:** the verify stage CONFIRMED
W5C-1 at MEDIUM; the consistency agent found W5C-1 and W5C-2 (the
same shape at the raw-fix rows, DOWNGRADED to LOW by its verifier)
cannot be scored differently and that on every measured axis
W5C-2's hazard ≥ W5C-1's — making the MEDIUM the outlier. The
critic (running in parallel, without the consistency output)
independently flagged the split as the thing clause 1 hinges on.
This report does not adjudicate the split: under either score the
remediation is identical, and §5's strict reading stands — wave 5
reported a MEDIUM.

## Failure clause: DID NOT FIRE

The critic checked rather than assumed: rows 83/183 were read by
no prior wave (wave-4 GAP 3 covered row 60's pin list only), so
this is a first-read surface, not a reopened audited one. The
two-population convergence diagnosis takes no damage — but the
propagation class above is the honest third finding population,
worth this section, not a diagnosis-reassessment doc.

## Clause-by-clause (critic's assessment, condensed)

1. **"Nothing above LOW" — NOT MET** (W5C-1, above).
2. **"Every in-model MEDIUM+ in the ledger fixed-and-pinned or
   user-accepted" — NOT MET.** The critic's own ledger sweep (no
   lane was charged with it) found six survivors with neither:
   OBL-1 (MEDIUM, live, mutation-demonstrated), W2-UNRUN-2 (HIGH
   label, live at `Signature.hs:551-559`, marked CONFIRMED-DEBT
   only), F11 (partial), LIB-W2-3 (MEDIUM, pin "owed there" but no
   row), F8b, F12's successor. Two items DO meet the clause and
   set the standard: LIB-1 and the gate-path divergences. Also
   four stale-OPEN rows understating progress (F7, FXC-6, SHIP-2,
   SHIP-3 — all landed).
3. **Green-at-release-commit — MET AT HEAD BY INHERITANCE** (full
   sweep PASS at `e2d6b3871`; HEAD is a 27-line doc-only delta
   outside doc-claim-lint's scope — verified). Per-commit by its
   wording: any remediation moves the release commit and requires
   a fresh sweep.
4. **CI leg observed green — NOT MET, knowingly** (user deferred
   CI to merge; unmeetable offline by construction).

## Other findings (all LOW/INFO after verification)

- Conformance lane: W5C-2..W5C-9 — the raw-fix rows' withdrawn
  contract family cited as live authority; a stale `#reduce`
  parenthetical describing pre-S-1 behavior; a known-gap cause its
  own sidecar contradicts; a census gap the consistency agent
  CORRECTED UPWARD (the true uncited-directory count is 80, not
  22 — under-scoped in the finding, including the LIB-1 witness
  row and this arc's own CRITICAL pins); understating status
  drift; an undefined `realized` status value; "per field"
  over-reading in the new pin's row text.
- Delta lane: the composition of all seventeen commits is SOUND —
  gate order re-derived, 33 fail tokens exactly pinned-or-waived,
  zero dead waivers, walks/prunes/clean compose, byte-identity
  re-verified. Five LOW/INFO: the CP-3 ledger entry describes fix
  one of three (its waiver citation was deleted by a later
  commit); a staged-then-deleted `Generated.lean` rejects under
  the caller-contract token rather than the deletion token
  (fail-closed, wrong name); census/oracle "shared definition"
  claim is not what the code enforces (different walk semantics,
  same domain today); `replay-kernel-selftest.sh clean` can never
  remove anything (`$$` of the cleaning shell); ship-list
  sub-check (c) prints no verdict when an earlier check failed.
- Residue lane: fourteen dispositions, ledger-ready — two CLOSED
  (DEMO-8: the bindist ships the demo in the layout its `require`
  needs, sdist-only gap remains and no release path runs sdist;
  SHIP-6: already catalogued verbatim in residual-trust §3.2c),
  one converted from asserted to OBSERVED (trivgoal_deep's harm
  story, demonstrated by probe), the rest CONFIRMED at LOW/INFO
  as 0.03 carries. Two sharpenings: DEMO-7's drift does NOT fail
  closed (each copy is checked against its own goal copy — stays
  green while the demo demonstrates a stale obligation); the
  give-up DENYLIST has no live selftest row (trivgoal_deep fails
  the allowlist on its own — the denylist's evidence is the
  hand-mutation, recorded, not a row).
- FXC-2's stream unit pin: adjudicated DEFER TO 0.03 — it
  protects only which diagnostic an unrealizable stream fix is
  refused with; the false-positive image is kernel-refuted and
  the dispatch fail-closed twice over.

## Remediation path (the critic's, adopted)

1. **Documentation-propagation commit** (small/stable per the
   threat model's own fix rule): restate the five `*WithProof`
   rows and the raw-fix rows as `known gap`, drop the withdrawn
   contract families from Expected-contract columns (restoration
   hazard), fix W5C-3/4/6/9 and the four out-of-file instances
   (architecture.md, proof-cookbook.md, STATUS.md,
   FixRecognizer.hs Haddock) plus the SAWCorePrimitives.lean
   docstrings (W5C-7).
2. **Ledger pass**: close the four stale-open rows; give each
   clause-2 survivor a pin or a PROPOSED disposition for user
   acceptance (five read as defensible 0.03 carries; OBL-1 should
   get the pin — it is the one with a demonstrated mutation).
3. **Fresh full sweep at the new release commit** (clause 3 is
   per-commit).
4. **Clause 4 at merge** (user's decision, already made); record
   the W5-2 determination when the run lands.

Filed for 0.03, mechanism-shaped: a declaration-existence
resolution for doc-claim-lint (or comment-line exclusion), so the
propagation class becomes a check instead of diligence.

---

*Workflow: 7 agents (3 docket, 2 verifiers, consistency, critic),
all Opus, refute-by-default, repo untouched (one lane's gitignored
lake probe removed after use). Run `wf_ea3a9200-b1e`. A stray
gitignored `intTestsProbe/trivmsg/` dir noted by the consistency
agent was this session's own enumeration probe, since removed.*
