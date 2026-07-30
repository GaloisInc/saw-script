# Release gate — WAVE 4 audit (2026-07-30, HEAD `b5c75fd09`)

Five Opus docket lanes over the four items the wave-3 ledger
commissioned (`TODO.md` § WAVE 4 SCOPE), every CRITICAL/HIGH/MEDIUM
finding adversarially verified (refute-by-default, independent
re-derivation at the cited lines), plus — for the first time — the
two harness improvements this project's own audit history demanded:
a **cross-finding consistency agent** (the wave-3 lesson: the panel
held "no IO route survives GATE B" and "an IO route survives"
simultaneously) and severity scored against the now-citable threat
model (`residual-trust.md` § Threat model, decided 2026-07-30). 17
agents. This is the first wave in which "CRITICAL" has a definition
to be measured against rather than a mood.

**Verdict: FINDINGS — no CRITICAL, nothing release-blocking under
the threat model. But docket items 1 and 2 are NOT closed**, and
item 2 is *escalated*: the completeness critic proved (and I
re-verified at the cited lines) that the demo's CI gate cannot have
been green since 2026-07-18. Wave 5 inherits three named charges
(§6).

Raw findings: 29. After verification: 2 MEDIUM (one CONFIRMED, one
downgraded from HIGH), 27 LOW/INFO. The verifiers downgraded 8 of
the 9 findings they examined — the docket lanes over-scored in
exactly the direction the threat model was written to correct, and
the verify stage did the correcting. That is the process working,
with one caveat that is this wave's most important sentence: **the
downgrades of the two FixRecognizer coverage findings rest on a
claim no one has mechanically checked** (§3).

Finding IDs below are lane-prefixed: FXS (FixRecognizer soundness),
FXC (FixRecognizer coverage), DEMO (shipped demo), SHIP (cabal
ship-list), DC (delta composition). Lanes filed them all as "FR-n";
the ledger uses these disambiguated names.

## 1. The docket, item by item

### Item 1 — `classifyFixShape` (first charge): STRONG ON THE HASKELL SIDE, NOT CLOSED

Two lanes read all 461 lines of `FixRecognizer.hs`, the consumer
(`Term.hs:1300-1372`), both lowerings, the Lean-side obligations
they emit, and the 17 pinned recognizer tests.

**What holds, independently verified by both lanes from different
directions:**

- All three classify-returning paths trace to invariants the code
  establishes. No well-typed SAWCore term was constructed that
  classifies while its recursive uses are not strictly decreasing.
- Veto composition is correct: `combine` is Left-dominant (`:358-360`)
  — one bad use kills any number of good ones — and `Right True`
  is produced only downstream of the `isExactVar idxVn idx` gate.
- The consumer is fail-closed in every probed direction: the guarded
  alternatives fall through to a total catch-all that throws;
  under-applied `Prelude.fix` lands on `("fix", reject
  unsupportedFixReason)` (`SpecialTreatment.hs:871`), closing the
  wave-2 L-1 guard-bypass class here; `fix` has no `rawLogicalTwin`
  and no alternate emission route; no `catchError` exists in
  saw-core-lean.
- Enumeration rot resistance is genuinely good: all 14 ident tests
  are fully qualified with exact-arity list patterns falling through
  to a named `FixUnrecognized`; the recursive walk uses the DERIVED
  `toList (unwrapTermF t)` rather than a hand constructor list;
  `-Wall -Werror` makes a new `FixClass` constructor a compile error.

**Why the item is not closed (two reasons):**

1. The soundness-lane's headline conclusion — "the recognizer is a
   selection/diagnostic gate, not the load-bearing barrier, because
   a false positive yields an *undischargeable* kernel obligation
   (`H_prod`'s `lookback`/`faithful` fields), drawn through
   `Classical.choose` so it cannot be erased" — is asserted from
   reading `SAWCorePrimitives.lean:1396-1412/1511-1528` and **was
   never mechanically checked** (§3). Every severity in this item
   hangs on it.
2. The coverage lane surveyed roughly half of the project's own pin
   inventory for this surface (`CONFORMANCE.md:60`), missing among
   others `differential/fix_error_elem` — a live KNOWN GAP whose
   only evidence is a one-time manual `#reduce` from 2026-07-16
   (§5, GAP 3).

Surviving findings, all LOW/INFO after verification: **FXC-1**
(`:350` inner at-index guard unpinned — mutate it to `if True` and
all 17 unit cases plus every golden stay green; the wave-3
accept-side-pin shape), **FXC-2** (the entire Class-S guard family
unpinned, incl. `isIdentityStreamRead`, ":192, load-bearing" per its
own comment), **FXC-3** (the `:280-287` amendment-C comment — the
block `TODO.md` cites as this gate's specification — asserts two
checks the code does not perform; the correct rules live at
`:345-349` and in `2026-07-15_op3-successor-design.md:337-352`),
**FXC-4** (raw 24-char `Show TermF` truncation in user-facing
rejection text, golden-pinned at `llvm_s20hash_comp` log line 233;
one character from leaking a nondeterministic UID into a golden),
**FXC-5** (the canonical iterate refusal names a true-but-not-the-limit
cause; the honest message at `:194-196` is unreachable for that
shape), **FXC-6** (unqualified `"Stream"` name test at `:167-168`,
out-of-model), **FXC-7/8** (unreachable `fixVerdictReason` equations;
the `:302-310` unvisited-slot enumeration is itself incomplete),
**FXS-1** (the at-index test is scope-blind: correctness rests on
the global `VarIndex` uniqueness invariant, `Name.hs:249`, which the
module never states as an assumption — out-of-model today, but a
future normalizer change reusing binder indices would silently widen
the gate), **FXS-2** (the walk's actual blind-spot set is larger
than its own `:303-310` note records).

### Item 2 — the shipped demo: ESCALATED, NOT CLOSED

The lane ran the demo's emission half on a scratchpad copy at HEAD:
all five `out/` files produced, and the committed
`Emitted.lean` copies are token-identical to fresh emission (equal
whitespace-stripped hashes) — the demo's discharge targets are
current, and the lane simulated every kernel text gate the demo's
replay path must clear (all pass). Staleness against the D2-D4
kernel is near-clean: no retired fail tokens, no old lint scope, no
`#check` probes.

Eight findings survived, all in-model documentation/workflow errors,
all LOW/INFO after verification: **DEMO-1** (the README's only
runnable Step-1 command block omits `SAW_LEAN_ROOT`; probe-confirmed
hard abort at the replay steps — though the error message itself
names the remedy, and Step 1's promised `out/` deliverables all land
before the abort, hence the downgrade), **DEMO-2** (README Step 3
walks the user into the 4.29.1-vs-4.32.0 shared-library clobber
unwarned — real doc gap, but the verifier showed the failure is
loud, gitignored-artifact-only, healed by the next 4.32.0 build, and
note the demo's Step 1 *already* clobbers via replay's own `lake
build` at `lean-check-core.sh:217`, so a Step-3 warning alone would
not cover the flow), **DEMO-3** (demo.saw's header says `out/Rev.lean`
is NOT produced; its own step 3b, the README, and the actual run say
it is), **DEMO-4** (demo trust story frozen at 2026-07-18: "closer-type
probe" is the retired idiom the A-5 fix removed; no pointer to the
threat model, LIB-1, or the re-run-replay-yourself evidence caveat;
the demo README never links `saw-core-lean/README.md` at all),
**DEMO-5** (require-path prose off by one directory level, twice),
**DEMO-6** (Files section misattributes `idBool`, undercounts
properties, omits `rev_impl.cry` and `depanalysis.saw` — the latter
documented nowhere live), **DEMO-7** (two unpinned byte-identical
copies of each tactic and goal; CI comment cites a `proof/README`
that does not exist), **DEMO-8** (demo not in any ship list while
shipped prose calls it canonical).

**The escalation (completeness critic, re-verified by me at HEAD):**
`.github/workflows/ci.yml:817-833` — the only CI gate on the demo —
runs `saw demo.saw` with **no `SAW_LEAN_ROOT` anywhere in
`.github/`** (grep: zero hits), on a `dist/bin/saw` lifted out of
`dist-newstyle` by `extract_exe` (`.github/ci.sh:12-19`) with a
baked-in, never-installed `~/.cabal/share` datadir. `demo.saw:66,69`
have called `offline_lean_replay` since 2026-07-18, and
`resolveLeanReplayAssets` (`Builtins.hs:1461-1479`) has exactly two
branches — env var, else datadir + `fail`. The demo-consumer lane
reproduced precisely this abort locally with the same binary
provenance (exit 2). The leg is a real matrix entry
(`ci.yml:206`) with `continue-on-error: [false]` (`:699`).
**Therefore exactly one of two unrecorded facts is true: the
`saw-core-lean-tests` CI leg is red at HEAD, or that leg is not
actually running in the configuration the release is cut from.**
Neither is in the ledger; this sandbox has no network egress, so
which one holds is a wave-5 determination. Either way: the demo's
replay half — one of only two user-authored proof-side surfaces
gated solely at demo time (`proof/replay/{invol,eq}/proof.lean`) —
has had no functioning CI gate for twelve days. The remedy is one
`export` line in ci.yml or two `cp` lines in `bundle_files`.

### Item 3 — the cabal ship-list: COVERED, with the wave's only CONFIRMED finding

Completeness at HEAD is **exact**: `git ls-files` over
`saw-core-lean/{lean,replay}` yields precisely the 4 + 7 + 3 files
the stanza names; `CryptolToLean/` has no subdirectories, so the
non-recursive glob currently misses nothing; no listed entry is
dead. The runtime consumer set is closed: every file the replay
pipeline opens is either in `data-files` or created at runtime. The
lakefile/manifest/toolchain pins are mutually consistent. Two
candidate findings were refuted outright by the lane itself (a
locale-encoding crash — killed by `setLocaleEncoding utf8` in both
mains; manifest inconsistency — none).

- **SHIP-1 (MEDIUM after verify, was HIGH)** — the official binary
  distribution never contains the data-files: `bundle_files`
  (`.github/ci.sh:167-182`) copies nothing from `saw-core-lean/`,
  the binary bakes a build-machine datadir, and no `cabal
  install`/`sdist` exists anywhere in `.github/`. `offline_lean_replay`
  is unusable in the release tarball while the help text
  (`Interpreter.hs:5333`) and `STATUS.md:359` say otherwise, and its
  own abort message ("Reinstall saw…") prescribes remedies the
  tarball user cannot take. Downgraded from HIGH because it fails
  closed and loud, the tarball's own docs barely advertise the
  feature, and the fix is two `cp` lines — but per GAP 2 this same
  defect breaks the project's own CI, which is why the MEDIUM should
  be revisited by wave 5 rather than filed as friction.
- **SHIP-4 (MEDIUM, CONFIRMED — the wave's only CONFIRMED verdict)**
  — the XDG cache staging race. `staging-tmp-<fpTag>` is named only
  by the content fingerprint (`Builtins.hs:1497`), and
  `removeDirectoryRecursive` fires unconditionally on a leftover
  (`:1498-1499`): two concurrent same-fingerprint processes share
  one tmp path, and the verifier found an interleaving the lane
  missed, **in the unsafe-for-availability direction**: P1 resumes
  its `copyFile` loop into P2's recreated tree, writes `.staged-ok`,
  and renames a marker-bearing tree *missing the head of
  `relFiles`* into `cacheDir`. Since the marker short-circuits every
  later run, the hole is permanent — `CHECK-FAIL:
  support-library-build` until the user hand-clears an XDG path.
  Still fail-closed (never an unsound acceptance), hence MEDIUM
  availability, not HIGH. Contrast: the per-call stage dir and the
  kernel's `WORK` dir both already use per-call uniquifiers.
- **SHIP-2 (LOW after verify)** — the entire data-files branch of
  `resolveLeanReplayAssets` is executed by no test: `lean-driver-test.sh:34-37`
  defaults and exports `SAW_LEAN_ROOT` unconditionally, so
  `Builtins.hs:1467-1508` is dead under every suite. The verifier's
  downgrade is instructive: it *executed the branch* (synthetic
  datadir from the stanza + `saw_datadir` + `XDG_CACHE_HOME`,
  `env -u SAW_LEAN_ROOT`) and it works end-to-end at HEAD, cold and
  warm — matching the implementation-time verification recorded at
  `2026-07-24_todo-execution-record.md:566-574`. So: "unexercised by
  CI", not "broken". A ~10-line row would close it permanently.
- **SHIP-3 (LOW after verify)** — the ship set is duplicated between
  `saw.cabal:42-46` and `relFiles` (`Builtins.hs:1482-1485`) with no
  mechanical check; the verifier narrowed it (the library half is
  derived at runtime from the installed tree and cannot drift; only
  four constant strings are duplicated; both drift directions fail
  closed). The lane's sketched `ship-list.sh` closed check is filed
  with the finding.
- **SHIP-5/6 (LOW)** — unguarded `listDirectory`/`readFile` after
  the single `doesFileExist` probe (raw IOException on partial
  installs); no toolchain verification anywhere in the kernel and
  the evidence's `leanReplayToolchain` is a file read, not an
  observation of the elaborator that ran.

### Item 4 — delta composition over the 2026-07-30 commits: COVERED

The lane walked `lean-check-core.sh` top-to-bottom at HEAD and
re-derived every ordering precondition the D2+D3+D4 interaction
touches: staging digests before text gates before first elaboration;
deletion-aware `verify_unchanged` reached unconditionally on every
path; `__drift_binding` lives only in checker-generated files the
lint never reads; the D4 deletion guard cannot over-fire; the
comment-separator invariant holds in every glue direction it could
construct; the meta-guard enumerates all 31 fail tokens; `completed_ok`
is a genuine accept-side pin; both drift-probe branches have live
accept-side rows. Token agreement across replay/, otherTests/,
intTests/ and saw-boundary is clean.

Five findings, all LOW/INFO after verification: **DC-1** (the trust
authority's §3.2b claims universal digest re-verification that the
same document's CP-1 row records as *discarded* — `Emitted.lean` is
verified once at `:223` and consumed by three later gates unverified;
the verifier showed every concrete bypass is backstopped (the olean,
not the text, feeds later elaboration; the drift probe and the
re-verified completed.lean sorry re-scan close the two grep gates),
so this is prose over-breadth, not a gap — but `:698` and
`TODO.md:689` should be narrowed to the gates the B1 fix actually
covers), **DC-2** (the D2 token rename reproduces the C2 defect it
was made to fix: six non-axiom lexer rejections — raw string,
interpolation, non-ASCII prime, ambiguous quote, two unterminated-at-EOF
— all emit `CHECK-FAIL: axiom-decl-in-user-file` for files
containing no `axiom`; measured at HEAD), **DC-3** (the lint's two
END-block lexer-state guards are the only lexer outcomes with no pin
after the 17-row retirement — and they enforce the F1 invariant;
independent catch exists via `proof-does-not-elaborate`, hence LOW),
**DC-4** (a third stale ledger pointer to the retired
`replay_reject_notation` row at `TODO.md:1730-1733` — the commit
that annotated the other two says "two"), **DC-5** (the D2 zero-cost
measurement has two irreconcilable denominators, 103 vs 112; the
lane re-ran the sweep: true figures 112 files, 3 flagged, all
deliberate fixtures, 0 of 109 legitimate).

## 2. The consistency agent: the wave-3 harness lesson, landed and vindicated

Four contradictions found; the agent resolved each at the code
itself rather than adjudicating prose. None changes a blocking
status, but two would have put false coverage claims into the
ledger:

1. **SHIP-2's verifier vs SHIP-4's verifier** on the same 15 lines:
   "a marker-bearing cache dir is necessarily complete" vs the
   confirmed marker-plus-hole interleaving. **The code supports
   SHIP-4**; the completeness clause holds only single-process and
   must be struck from SHIP-2's reasoning (its LOW stands on its
   other grounds).
2. **The `in_model` column was scored under two mutually exclusive
   rules** — nine findings treated `residual-trust.md:32-49`'s three
   bullets as an exhaustive classifier (doc-only defect ⇒
   out-of-model); four treated in-model as the complement of
   "adversarial". **The threat model's only normative scoring
   sentence (consequence 1, `:64-69`) keys on one question — does
   the defect require an adversarial author? — so Rule B is
   operative**: doc-only defects are in-model. Residue: score them
   one way in the ledger, and add one sentence at `:62` for defects
   that are not evasion routes at all — the missing category that
   produced the divergence.
3. **SHIP-1's verifier vs SHIP-2's verifier** on whether data-files
   mode is in release scope (each moved severity on its reading).
   `saw.cabal:31-40`, `architecture.md:36-37`, and `STATUS.md:358-360`
   all present data-files mode as the shipped default; SHIP-1's
   "documented supported mode is a checkout" ground is struck (its
   MEDIUM survives on its other grounds).
4. **DEMO-2's verifier claimed a guard-by-sequencing** ("every
   harness runs `lake build` before `lake env lean`") **that does
   not exist in sweep mode**: all five build sites sit inside
   `SAW_LEAN_SUITE_LAKE_PREBUILT` skips, and `test.sh:438` sets that
   var after ONE build at sweep start — which is exactly why the
   recorded 2026-07-29 incident (16 spurious failures) happened the
   day *after* the prebuild hoist landed. DEMO-2 stays LOW on its
   other grounds; the sequencing claim must not enter the ledger as
   coverage.

The agent also examined eight further candidate pairs and found them
consistent — including confirming that the two fixrec lanes' explicit
hand-off (over-refusals named by the soundness lane, reported by the
coverage lane as FXC-6) worked as designed.

## 3. The caveat that bounds this wave: the H_prod discrimination claim (GAP 1)

The wave's central severity move — FXC-1 and FXC-2 from MEDIUM to
LOW, and the soundness lane's whole "diagnostic gate, not
load-bearing barrier" framing — rests on: *a recognizer false
positive yields an undischargeable kernel obligation*. The
completeness critic checked what evidence exists for that claim:

- `lookback` and `faithful` — the fields both verifiers called "the
  sole loud-failure discriminator" — appear **zero times in
  otherTests/**.
- Every corpus occurrence of the obligation is an ACCEPT-side
  discharge (five `completed.lean` rows). **No row anywhere attempts
  and fails to discharge `H_prod` for a wrongly-admitted body.**
- The two negative rows whose directory names advertise this
  contract (`negative/fix_contract`, `negative/fix_obligation_erasure`)
  pin only S-1 seed-binding — and were read by no lane.
- No generic discharger exists that would make H_prod cheap (all 19
  occurrences in `SAWCorePrelude_proofs.lean` take `H` as a
  hypothesis) — so the claim is *plausible from the definitions*.
  Plausible-from-reading is exactly the evidence standard rule C4
  rejects for a load-bearing guard.

If the claim is wrong, or a future `SAWCorePrimitives.lean` edit
makes it wrong, FXC-1/FXC-2 revert to MEDIUM in-model emission
defects with unpinned admission guards, and the wave's severity
distribution collapses with them. **FXC-1 and FXC-2 are therefore
recorded LOW-provisional, dependent on a wave-5 reject-side pin**: a
~15-line `.shouldfail` row that tries to prove `H_prod` for the
FXC-1 witness body (`at rec (addNat i2 1)`, result[i] = rec[i]) and
pins the failure. That single row converts the wave's argument from
reading to evidence.

## 4. Scoring discipline under the threat model

First wave with the citable threat model. Observed effect: the
verify stage downgraded 8 of 9 examined findings, in every case by
separating "real defect" from "reachable consequence" — the exact
split the model was written to force. The two-rule `in_model`
divergence (§2, contradiction 2) is the model's one exposed seam;
its fix is a sentence. Two in-model items escaped scoring entirely
(the CI demo step; `fix_error_elem`'s manual-only evidence) because
they sat between lanes — both now carried by wave 5.

## 5. What this wave did NOT establish

- **GAP 1** (§3): no reject-side evidence that H_prod discriminates.
- **GAP 2** (§1 item 2): whether the `saw-core-lean-tests` CI leg is
  red or unrunning — undeterminable without network; either is
  release-relevant and unrecorded.
- **GAP 3**: the coverage lane surveyed ~half of `CONFORMANCE.md:60`'s
  designated pin set for the audited surface (missed
  `differential/fix_classS_eval`, `fix_error_elem`,
  `saw-boundary/fix_obligation`, the four obligations/ rows, and
  three workflows/ rows carrying `saw_fix_bounded_*` goldens). Its
  "nothing lets an unsound shape through at HEAD" is a
  partial-survey result. `fix_error_elem` specifically: a SAW-vs-Lean
  agreement claim for an error-carrying element inside a recognized
  Class-F fix, whose only evidence is a one-time manual `#reduce`
  from 2026-07-16, with four backend deltas landed since — squarely
  in-model, never scored.
- The demo tactic's actual closure in Lean (needs the prohibited
  `lake build`) — everything up to elaboration was simulated and
  passes.

## 6. WAVE 5 CHARGES (inherited)

1. **Reject-side H_prod pin** — the `.shouldfail` row of §3.
   Discharges the provisional status of FXC-1/FXC-2 (or reverts them
   to MEDIUM and reopens docket item 1 at that severity).
2. **Determine and fix the CI demo step** — is the leg red or not
   running? Then one `export SAW_LEAN_ROOT="$GITHUB_WORKSPACE"` in
   `ci.yml:821`, or ship the data-files in `bundle_files` (which
   also remedies SHIP-1 for tarball users — revisit SHIP-1's MEDIUM
   in whichever light).
3. **Cross-check `CONFORMANCE.md:60`'s inventory** — open every row
   the coverage lane skipped; re-establish or reclassify
   `fix_error_elem`'s manual observation.

Fix-shortlist (non-blocking, small/stable per the threat model's
own rule): SHIP-4 uniquify or lock the staging tmp dir (mirror the
kernel's `replay-$$-…` pattern); DC-2 split the lexer-rejection exit
from the axiom token (or rename to cover both truthfully); DEMO-1/2/3
one-command README fixes + a clobber warning; DEMO-4 link the trust
story and drop the retired "closer-type probe" phrasing; FXC-3
rewrite `:280-287` to the rules at `:345-349`; DC-1 narrow
residual-trust §3.2b:698 and TODO.md:689; DC-4 annotate the third
stale pointer; the `in_model` sentence at residual-trust `:62`;
SHIP-3's `ship-list.sh` closed check; SHIP-2's ~10-line data-mode
row.

---

*Workflow: 17 agents (5 docket lanes, 9 verifiers, consistency
agent, completeness critic), all Opus, refute-by-default, probes
scratchpad-only, repo untouched. Run `wf_bf879d1f-ebc`. All
severities cite `residual-trust.md` § Threat model (decided
2026-07-30).*
