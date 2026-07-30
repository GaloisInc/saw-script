# Why the audits aren't converging, and the proposal (2026-07-29)

Written in answer to a direct question — *are we converging?* — after
three audit rounds in one day. The honest answer is **not on defect
count, but the reason is now identifiable and single**, which is a
much better position than it sounds.

This note is a proposal, not a decision. It ends with what I would do,
what it costs, and what I am least sure of.

## 1. The measurement

Every audit round since 2026-07-21 has found at least one CRITICAL.
That alone reads like divergence. But sorting them by *whether the
class was already known* tells a different story:

| round | CRITICAL | class |
|---|---|---|
| 07-21 review | F1 | **NEW** — lint blinded by a string literal |
| 07-23 fidelity | bvToInt | **NEW** — signed/unsigned realization |
| 07-24 panel ① | R-1 | **NEW** — replay goal binding |
| 07-24 panel ② | A-1/A-2/A-5 | R-1 "was one instance of a CLASS" |
| wave 1 | B1 elaboration order | **NEW** — order, not membership |
| wave 1 | B2 F-5 nested sort | KNOWN (F-5), member unswept |
| wave 2 | LIB-W2-1 IntMod | KNOWN (F-2), member unswept |
| wave 2 | W2-MAP-1 bare names | KNOWN (F-6/F-7), enumeration incomplete |

Three of the last four are not discoveries. They are **members of
classes we had already named, fixed, and closed.**

## 2. The single cause

Each of those classes was closed by **hand-enumerating its members**,
and every hand enumeration rotted:

| class | closed by | what survived |
|---|---|---|
| F-2 | sealing the two types the audit named | `IntMod` |
| F-6/F-7 | `hardcodedBareNames`, "a hand-listed set" | the ~30 contract names |
| F-5 | gating binder types that *are* sorts | sorts *inside* binder types |
| F-1 | five hand-identified `== BindingFunction` sites | the sixth site |
| Slice-7 lint | a hardcoded eleven-file list | the three new modules |

Five for five. Not five unlucky misses — one mechanism failing five
times.

The mechanism is subtle because each closure *was* correct when
written. `hardcodedBareNames` listed every bare name that existed in
July. The Slice-7 lint listed every source file that existed. They
did not become wrong through carelessness; they became wrong because
**the code grew and the list did not**. A hand enumeration encodes a
snapshot of the world into a file that has no reason to change when
the world does.

Worth noting explicitly: I wrote three of the five. This is not a
review-quality problem that better reviewers would have caught. F-1's
missed site was found only because an auditor was told to enumerate
the sites independently rather than check my list.

## 3. The lever already exists in this tree

`adaptTo` is the existence proof. It closed its class **by
construction** — forbidden adaptations are unrepresentable rather than
listed — and across five audit rounds it has produced **no defect of
its class**. The Family-3 analysis says so in as many words, and
nothing since has contradicted it.

The replay coverage meta-guard is the second proof: it enumerates
every `fail "..."` in the trust kernel and demands a case or an
explicit waiver. When I added two new guards during the wave-1 fixes,
it flagged both as unpinned *before any auditor saw them*. That is
what convergence looks like from the inside.

Three fixes landed today are the same move:

- `contractEmittedNames` — derived from the contract tables
- `lintSourceFiles` — derived from a directory walk
- `lib1-census` — re-derived from the corpus on every run

## 4. The proposal

**Convert the remaining soundness-gating hand enumerations to derived
ones, then audit.** The order matters: an audit against a derived
enumeration can only find *new classes*, while an audit against a
hand-listed one will keep finding unswept members indefinitely — and
will keep costing a full panel to do it.

The remaining list is short and known:

| enumeration | where | members | derive from |
|---|---|---|---|
| `lintForbiddenNames` | SmokeTest.hs | ~20 | a tombstone marker in the source, so deleting a heuristic registers it |
| `supportLibraryFiles` | SmokeTest.hs | ~8 | directory walk of `lean/CryptolToLean/` |
| `lintSelfMirrorCeilings` | SmokeTest.hs | 3 | measured, with exact counts (as the `"Except"` ceiling now is) |
| `leanOpaqueBuiltins` | SpecialTreatment.hs | — | cross-checked against the Prelude, both directions |
| `is_waived` | replay-kernel-selftest.sh | ~2 | already has the meta-guard; make each waiver carry a reason string it must match |
| `hardcodedBareNames` residue | SpecialTreatment.hs | ~30 | the emitter's own writes — needs a marker at each emission site |

Three of these are an afternoon. `hardcodedBareNames`' residue and
`leanOpaqueBuiltins` are the real work, because "every name the
emitter writes bare" is not derivable from a table today — the emitter
writes some names as string literals at the point of use. That one
probably needs a small newtype so a bare emission cannot be spelled
without registering itself.

**A second, cheaper habit, and I would adopt it regardless:** when an
audit finds an instance, the closing commit must say *how the class
was enumerated*, and that sentence must name a mechanism, not a list.
"I checked all the sites" is the sentence that preceded every one of
the five failures above. This is the A-3 discipline — a claim needs a
mechanism — applied to closure claims rather than to soundness claims.

## 5. What this predicts

> **SCORED 2026-07-30 — the prediction FAILED; see §8 for the
> corrected diagnosis.** Original text kept unchanged below.

If the diagnosis is right, **wave 3's CRITICALs will be in the six
enumerations above**, and nowhere else. That is a falsifiable
prediction and I would treat it as the test of this whole analysis.

If wave 3 instead finds a CRITICAL in a *derived* enumeration or in a
by-construction chokepoint, the diagnosis is wrong and the problem is
deeper than enumeration discipline.

## 6. What I am least sure of

> **SCORED 2026-07-30:** the first bullet's worry did NOT
> materialize — wave 3's claimed sixth member (`bitvector`) was
> itself refuted post-audit
> (`2026-07-30_bitvector-claim-refuted.md`); the sweep stands at
> five. The last bullet was the load-bearing one: Family 1 is
> where the prediction actually failed. See §8.

- **The `IntMod` sweep is my own claim.** I asserted that the
  opaque-primitive-vs-reducible-alias class has exactly five members
  and is now closed. If wave 3 finds a sixth, then section 2's whole
  story is too optimistic — the problem would not be that
  enumerations rot, but that I cannot enumerate reliably even when
  I am specifically trying to.
- **Nine data points.** The pattern is strong but the sample is one
  project over about ten days, and I authored a third of it.
- **Derivation has its own failure mode.** A derived enumeration is
  only as good as its source of truth. `lib1-census` derives from
  "untracked `.lean` files" and I have already had to widen its
  diagnostic once because uncommitted probes counted as emitted.
  Deriving moves the assumption; it does not delete it. The reason to
  prefer it anyway is that a derived enumeration fails *loudly and at
  once* when its assumption breaks, where a hand list fails silently
  and months later.
- **This does not touch the two deferred families.** Family 1 (the
  trust kernel asking text questions) and Family 2 (no model of SAW's
  partiality) are deferred by decision and are not enumeration
  problems. Nothing here makes them smaller.

## 7. Recommendation

1. Do the three cheap conversions now (`supportLibraryFiles`,
   `lintSelfMirrorCeilings`, `is_waived` reasons).
2. Scope the two real ones (`hardcodedBareNames` residue,
   `leanOpaqueBuiltins`) as one piece of work with a design note —
   they share a root, which is that the emitter can write a name
   without registering it.
3. Adopt the closure-claim rule in §4.
4. **Then** run wave 3, and use §5 as its scorecard.

## 8. Postscript (2026-07-30): the prediction failed, and what the failure taught

Wave 3 ran with §5 as its scorecard
(`2026-07-30_release-gate-audit-wave3.md`). The prediction failed in
both directions:

- **K-2** is a CRITICAL in a *chokepoint* (the digest guard /
  path-selection logic of `lean-check-core.sh`), not in any of §4's
  six enumerations.
- **W2-UNRUN-1** — reinstated after my wave-2 non-reproduction was
  shown to be a single-test-case artifact — is a second chokepoint
  CRITICAL, reachable from ordinary Cryptol.
- Even the *confirming* finding, K-1, lives in
  `proof-source-lint.awk`'s ban list, which §4's table does not
  contain. "In the six and nowhere else" was false even where the
  diagnosis looked right.

### What survives

The enumeration-rot story is **correct for the translator**. The
derived conversions held; `adaptTo` is now six audit rounds without
a defect of its class; and §6's first worry dissolved — wave 3's
claimed sixth type-collapse member (`bitvector`) was refuted
post-audit (SAWCore declares no such type;
`2026-07-30_bitvector-claim-refuted.md`), so the five-member sweep
stands. By the only measure this note proposed, **the translator
converged**.

### What was wrong

§1 treated all CRITICALs as one population with one cause. They were
two populations:

- **Emission-side** defects (the translator) — enumeration rot,
  fixed by derivation, converged as predicted.
- **Trust-kernel** defects — a different mechanism entirely. The
  kernel's text-inspection guards were defending against an
  *unstated* threat model (an adversarial proof author), a job text
  inspection cannot do; and fixing them generated new defects at
  roughly 1:1 (the B1 fix introduced K-2 and CP-1; three fix-audit
  rounds each found defects in the fix under audit). §6's last
  bullet — "this does not touch the two deferred families" — was
  the load-bearing caveat: Family 1 is exactly where the prediction
  failed.

### The replacement

Convergence for the kernel was achieved by **scope reduction, not
further fixing** (user decision, 2026-07-30, D1–D4 in the decision
log): the threat model is now fixed as *error, not adversarial
action* (`2026-05-02_residual-trust.md` §Threat model), under which
the kernel's remaining CRITICALs re-score as out-of-model; the
proof-source lint narrows to its one closed check; the
kernel-checked ask-Lean gates (binding theorem, axiom audit,
hardened drift check) carry the load. The in-model CRITICAL wave 3
surfaced (W2-UNRUN-1) was emission-side and was closed the same day
by goal-shape gate 3 — i.e. by this note's own discipline, on the
population where that discipline actually applies.
