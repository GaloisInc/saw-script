# Soundness review of recent additions (2026-07-21)

Independent multi-reviewer soundness review of the additions that had
landed without prior independent review. Three reviewers, each on a
distinct surface, fresh context (not the implementing session). Goal:
find any path by which the translator or the proof-acceptance machinery
lets a Lean proof succeed while the corresponding SAW statement is false
or has different semantics. Loud failure (elaboration error, rejection)
is acceptable by design; silent divergence is the target.

## Surfaces and verdicts

| Surface | Commits | Verdict |
|---|---|---|
| Type-image obligation mechanism, rawLogicalTwin, raw head/tail | 03a5f91a4 | SOUND (2 standing conditions, pre-existing/enforced) |
| Primitive realizations (proveLeNat/natCompareLe, IsLeNat/IsLtNat, Maybe/Either, intAbs/min/max, eqNat, EmptyVec) | 4e0f404a4, 0aa9cd73a, adb19d2fe | SOUND (1 forward-looking condition) |
| Trust-tier acceptance machinery | b1a8b3cae, deefbefad | ONE CRITICAL FINDING (F1), confirmed |

## Findings

### F1 — CRITICAL, confirmed (re-verified independently)

**Mechanism:** `saw-core-lean/replay/proof-source-lint.awk`. The lint's
block-comment scanner tracks `/- … -/` nesting with no awareness of
string or character literals. A proof-side file containing a string
whose contents include the comment-open sequence (e.g.
`def cmt : String := "/-"`) drives the scanner into comment-skip mode
mid-string; it then treats all subsequent source — across line
boundaries, through end of file — as comment text. A real `axiom`
declaration after that point is never scanned, and the lint exits 0.

**Why this is a soundness bug, not a loud-failure nit:** the source
lint is the sole defense that stops a hand-written `axiom` from reaching
the axiom audit under the `native-eval` trust tier. That tier admits any
residual axiom whose name matches
`^goal_(holds|closed)\._native\.bv_decide\.ax_[0-9_]+$`
(`axiom-audit.awk`). A proof author can declare
`axiom goal_holds._native.bv_decide.ax_1 : goal` directly at top level
(hierarchical names need no enclosing namespace — the claim in commit
`deefbefad` that a namespace is required is incorrect), hide it behind
the string-literal blind spot, and close the goal with it. The hand-declared
axiom then passes the audit as a tier-admitted name. Net effect: any
false theorem is accepted on a `native-eval` row.

**Acceptance path (layers that pass but should reject):**
source lint (evaded) → residual-sorry scan (none present) →
closer-type check `#check (goal_closed : goal)` (a hand-declared axiom of type
`goal` satisfies it) → anti-trivialization (checks the goal shape, not
the proof) → axiom audit (name admitted by the tier) → vacuity guard
(one closer, one audit line) → CHECK-OK / exit 0.

**Confirmed on both consumers:** the product trust kernel
`replay/lean-check-core.sh` and the CI harness
`otherTests/saw-core-lean/support/lean-proof-test.sh`. Independent
re-verification (this session): the lint exits 0 on a file declaring
`axiom sneaky : (1:Nat)=2` preceded by a `"/-"` string; the same file
without that string exits 1 (correctly caught).

**Scope / live exposure:** latent, not a live false-green. Triggering it
requires a proof author to deliberately write both the string and the
matching-named axiom; none of the five landed tier rows
(`llvm_chacha20_q_eq`, `llvm_salsa20_q_eq`, `_pt0/1/2`) do so, so the
current suite is not masking any unsound acceptance. Safe to fix
deliberately rather than under time pressure.

**Fix direction:**
1. Immediate: make the lint's scanner literal-aware — skip Lean string
   and char literals (including `"…"`, `r"…"`/raw and `s!"…"`
   interpolations, and `'…'`) before looking for comment delimiters.
   Add a regression case (comment-open sequence inside a string
   followed by a banned declaration) to
   `support/trust-tier-selftest.sh`; the current 15 cases miss it.
2. Structural (preferred long-term): stop admitting axioms by name
   pattern. Any author can choose an axiom's name, so a name-pattern
   allowance can inherently be satisfied by a hand-declared name at the source layer. Instead,
   establish that a residual `native-eval` axiom genuinely originates
   from a harness-run `bv_decide` invocation on the row's own goal —
   e.g. re-run the discharge under harness control and compare the
   produced native-axiom set, rather than trusting names in the
   author's file.

**FIXED (2026-07-21, same day).** `proof-source-lint.awk` was
rewritten as a character-level state machine tracking nested block
comments, line comments, plain string literals (escape-aware,
multi-line), and char literals, with prime-vs-char-literal decided by
token tracking. Its soundness invariant: never in literal/comment
state while Lean's lexer is in code state; every construct where
byte-level tracking cannot CERTAINLY agree with Lean's lexer is
rejected loudly instead of guessed (raw strings, interpolated
strings, primes on tokens containing non-ASCII characters, the
genuinely ambiguous `]'X'` — Lean resolves checked-indexing-proof vs
char-literal by parser backtracking, probed empirically on the pinned
toolchain). This is sound because acceptance also requires the file
to elaborate: a file the lexer tracks differently from Lean either
rejects here or fails to compile. With source-level declaration
prevention airtight, the name-pattern admission is justified (a
residual tier-pattern axiom can only come from a genuine bv_decide
run), which discharges the structural concern in fix direction 2.

The fix pass also closed four adjacent holes the review had missed:

- **Escape-hatch tokens**: the ban list lacked `run_tac` (arbitrary
  `TacticM` from inside a proof — can `addDecl` an axiom exactly the
  way `bv_decide` itself does), `#eval` (elab-monad actions),
  `builtin_initialize` (slipped the `initialize` token boundary), the
  `@[csimp]` attribute (swaps implementations used by native
  evaluation, which the native-eval tier leans on), and
  `debug.`-namespace options (`debug.skipKernelTC` suspends kernel
  checking of added declarations). All banned; the lint header
  requires re-reviewing this list on every toolchain bump.
- **awk-crash = silent pass**: UTF-8-locale awk can hard-error on
  some multibyte input with empty output, and both consumers treated
  empty output as a pass. Both now run the lint under `LC_ALL=C`
  (byte mode, which the taint rule assumes) and reject on any nonzero
  awk exit regardless of output.
- **Selftest coverage**: `trust-tier-selftest.sh` grew from 15 to 27
  cases — the end-to-end F1 regression (string-hidden axiom on a tier
  row) plus a pure-lint battery (escape hatches, cannot-classify
  rejections, and a no-false-positive acceptance of every legitimate
  landed shape: strings containing banned words, identifier primes,
  escaped char literals, `xs[i]'h`).
- The minor LEAN_PATH asymmetry below was folded in as planned.

### C1 — IsLeNat constructor/recursor mapping hazard (condition, sound today)

`IsLeNat` maps to Lean's `Nat.le` and this is sound as used. But the
constructors and recursor do **not** line up structurally:
SAWCore `IsLeNat_succ` takes `m` explicitly (`Prelude.sawcore:1391`)
whereas Lean `Nat.le.step` takes it implicitly, and `IsLeNat__rec`'s
argument shape (`Prelude.sawcore:1399-1405`) does not match
`Nat.le.rec`. Today these constructors and `IsLeNat#ind` are
deliberately unmapped and reject loudly (`SpecialTreatment.hs` reject
rows; pinned by `obligations/proof_is_le_nat_succ_succ/.known-gap`).
A future naive `mapsTo` of these would risk a silent misroute unless the
explicit/implicit `m` and the recursor argument shape are reconciled
first. **No action now** — recorded so the constant-headed-Prop work
(which touches this family) does not casually map them.

### C2 — support-definition faithfulness (condition, verified)

The only new trusted support definitions on the type-image surface are
raw `head`/`tail` (`SAWCorePrimitives.lean:441-447`); gen/foldr/foldl/
genWithBoundsM pre-exist. Verified by evaluation against
`Prelude.sawcore:1536-1537`: `head [10,11,12,13] = 10` (element 0),
`tail = [11,12,13]` (drop-first); both sides require
`Vec (Nat.succ n)`, so any shape mismatch is a loud Lean type error.

### Minor — consumer LEAN_PATH asymmetry (FIXED 2026-07-21)

The trust kernel `lean-check-core.sh` clears `LEAN_PATH` to the stage
dir; the CI harness `lean-proof-test.sh` appends the ambient
`${LEAN_PATH:-}`. Empty in clean CI, so not a live issue, but the CI
consumer would import from an ambient `LEAN_PATH` where the trust kernel
would not. Pin the CI consumer's `LEAN_PATH` to the stage dir only, for
parity. (Independent of F1.) **Fixed with the F1 commit: all three
invocation sites now pin `LEAN_PATH` to the probe dir only.**

## Coverage evidence (checks the designs survived)

Type-image surface: exact-arity guard routes under/over/bare
applications to loud rejection; emitted obligation preserves the full
`head 3 … (gen …)` structure (no collapse to `Eq x x`) and the
obligation value is contentful (`#eval`: LHS `ok 0`, corrupted RHS
`ok 1` differs); the obligation is a local `let h_proof_ : … := sorry`
consumed at the same site in the same mode, so obligation type and
consumer requirement match by construction; no reachable path emits
these names as a free Lean `axiom` rather than an obligation or a
rejection; rawLogicalTwin is mode-guarded (`not phase && module=Prelude`)
and the twin is semantically identical.

Primitive surface (each cites the SAWCore authority; most rfl- or
compilation-confirmed): proveLeNat/natCompareLe are genuinely
typing-only (`primitive … FIXME: implement this!`,
`Prelude.sawcore:1409,1430`; no simulator prim, no Rocq realization) so
any type-correct inhabitant is unfalsifiable; IsLeNat→Nat.le preserves
argument order; IsLtNat = IsLeNat (Succ m) n matches Nat.lt with no
off-by-one; equality-boundary arms correct (natCompareLe→Right, proveLeNat
→Just at m=n); Maybe/Either constructor order matches and is pinned;
Sort-polymorphism is strictly more permissive and Prop-content-preserving;
eqNat = @Eq Nat; intAbs/min/max = Haskell abs/min/max on unbounded
Integer (Concrete.hs/RME.hs); EmptyVec unique at Vec 0; unmapped
identifiers reject loudly.

## Disposition

- F1: **FIXED same day** (lexer-based lint + escape-hatch bans +
  awk-crash hardening + 12 new selftest cases; see the FIXED note in
  the F1 section).
- C1: standing note attached to the constant-headed-Prop work.
- C2: closed (verified).
- Minor LEAN_PATH: fixed in the F1 commit.
- Reviewers otherwise found the type-image and primitive surfaces sound.
