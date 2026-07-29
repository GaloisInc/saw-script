#!/usr/bin/env bash
#
# lean-check-core.sh — the FACTORED TRUST KERNEL for checking a Lean
# discharge against an emitted saw-core-lean goal. This is the single
# checker (replay design, 2026-07-16 + seventh-audit amendments):
# invoked by the SAW-side offline_lean_replay at product runtime, and
# intended target for the CI proof harness to delegate to. Any check
# added here protects both paths; any check added elsewhere is drift.
#
# Usage:
#   lean-check-core.sh <lean-project-root-abs> <stage-dir-abs> [trust-tier]
#
# trust-tier (optional, 2026-07-21): names a NON-STRICT axiom tier
# for THIS check only. The single authority for tier names and what
# each admits is axiom-audit.awk (currently: `native-eval` admits
# bv_decide's per-invocation proof-local native axioms). Omitted =
# strict, byte-identical behavior to before. Unknown tier names and
# declared-but-unused tiers fail loudly inside the audit.
#
# The stage dir must contain:
#   Emitted.lean     — the FRESHLY-EMITTED goal (authority; the caller
#                      strips the trailing `goal_holds := by sorry`
#                      stub so every remaining sanctioned placeholder
#                      is in-statement and axiom-audit-visible —
#                      seventh-audit amendment 3)
#   proof.lean       — the user's discharge (must name goal_closed)
#   completed.lean   — OPTIONAL completed outline; if present the
#                      caller must also stage Generated.lean (the
#                      reference emission wrapped in namespace
#                      GeneratedHarness) for the drift check. Both
#                      must carry the single emitted `def goal :` —
#                      goal-presence is decided by Generated.lean
#                      (the authority), and a completed outline that
#                      does not present the bare `def goal :` line is
#                      rejected outright (R-1 fix, 2026-07-24 audit)
#
# Environment: ambient LEAN_PATH is CLEARED (seventh-audit amendment
# 2) — Lean sees exactly the stage dir plus lake's own project paths.
#
# Output contract: on success, one line `CHECK-AXIOMS: <name>: [...]`
# per audited closer and a final `CHECK-OK`. On failure, a line
# `CHECK-FAIL: <named-check>` and nonzero exit. No silent outcomes.

set -u

PROJ="${1:?lean project root (absolute) required}"
STAGE="${2:?stage dir (absolute) required}"
TRUST_TIER="${3:-}"

fail() { echo "CHECK-FAIL: $1"; exit 1; }

if [ -n "$TRUST_TIER" ]; then
    echo "CHECK-TIER: $TRUST_TIER (non-strict axiom tier; authority: axiom-audit.awk)"
fi

case "$PROJ" in /*) ;; *) fail "project-root-not-absolute" ;; esac
case "$STAGE" in /*) ;; *) fail "stage-dir-not-absolute" ;; esac
[ -f "$STAGE/Emitted.lean" ] || fail "missing-emitted"
[ -f "$STAGE/proof.lean" ]   || fail "missing-proof"

# lake requires input files inside the package root, so the working
# stage is a PER-CALL-UNIQUE, gitignored dir inside it (the
# seventh-audit amendment's intent — no collisions, no checkout
# pollution — via uniqueness + cleanup rather than out-of-tree
# placement, which lake cannot serve). Caller-staged files are copied
# in; the dir is removed on every exit path.
WORK="$PROJ/.replay-stage/replay-$$-$(date +%s)-$RANDOM"
mkdir -p "$WORK" || fail "cannot-create-work-stage"
trap 'rm -rf "$WORK"' EXIT
for f in Emitted.lean proof.lean completed.lean Generated.lean; do
    [ -f "$STAGE/$f" ] && cp "$STAGE/$f" "$WORK/$f"
done
STAGE="$WORK"

# ---------------------------------------------------------------
# ORDERING INVARIANT (B1, 0.02 release-gate audit, 2026-07-29):
#
#   NO USER-AUTHORED LEAN IS ELABORATED BEFORE EVERY PURE-TEXT GATE
#   HAS RUN ON THE EXACT BYTES IT WILL LATER BE JUDGED ON.
#
# This used to be false, and it was a CRITICAL unsound-acceptance
# path. The gates below (the sorry scan and the source lint) sat ~140
# lines further down, AFTER step 1 ran `lake env lean` on
# `Emitted.lean`. On the completed-outline path the SAW caller stages
# the USER's `completed.lean` as BOTH `completed.lean` and
# `Emitted.lean` (Builtins.hs), so step 1 elaborated user-authored
# Lean as the kernel's FIRST Lean action.
#
# Lean elaboration executes commands. A `run_cmd` in that file runs
# arbitrary IO at that moment, while `$WORK/completed.lean` (the only
# copy the lint would ever read) and `$WORK/Generated.lean` (the
# drift check's AUTHORITY — the sole thing binding the user's `def
# goal` to the SAW obligation) both sit on disk, rewritable. Rewrite
# both and the run yields CHECK-OK for a false obligation.
#
# Two changes close it. FIRST, the pure-text gates move here: neither
# needs Lean or the built library, and both are the gates that exist
# precisely to keep hostile constructs out of the elaborator. They
# stay below `STAGE="$WORK"` so the lint's `sed "s|$STAGE/||g"` path
# stripping still produces the deterministic diagnostic driver
# goldens pin. SECOND, see the hash re-verification below: ordering
# alone is a property of where statements sit in this file, and a
# future edit could silently undo it, so the invariant is CHECKED
# rather than merely arranged.
# ---------------------------------------------------------------

# Non-degradable digest guard, same discipline as the timeout guard
# below: a trust kernel that cannot verify its inputs did not change
# refuses rather than degrading to trusting them.
if command -v sha256sum >/dev/null 2>&1; then
    digest() { sha256sum "$1" | awk '{print $1}'; }
elif command -v shasum >/dev/null 2>&1; then
    digest() { shasum -a 256 "$1" | awk '{print $1}'; }
else
    fail "no-digest-guard"
fi

# Record the bytes as staged, BEFORE anything has had a chance to run.
STAGED_DIGESTS=""
for f in Emitted.lean proof.lean completed.lean Generated.lean; do
    if [ -f "$STAGE/$f" ]; then
        STAGED_DIGESTS="$STAGED_DIGESTS$f $(digest "$STAGE/$f")
"
    fi
done

# Re-verify that a file still has the bytes the text gates saw. Called
# immediately before each gate that CONSUMES a file, so a rewrite by
# anything that ran in between is caught rather than trusted.
verify_unchanged() {
    local f="$1" want have
    [ -f "$STAGE/$f" ] || return 0
    want=$(printf '%s' "$STAGED_DIGESTS" | awk -v k="$f" '$1==k{print $2}')
    have=$(digest "$STAGE/$f")
    if [ "$want" != "$have" ]; then
        echo "$f changed after staging (expected $want, found $have)"
        fail "user-file-mutated-mid-check"
    fi
}

# GATE A (was step 4.5). Placeholder policy on the USER's files. See
# the long note at the original site below for why `sorry` is
# zero-tolerance on these two and not on Emitted.lean.
for uf in proof.lean completed.lean; do
    if [ -f "$STAGE/$uf" ] && grep -qn 'sorry' "$STAGE/$uf"; then
        grep -n 'sorry' "$STAGE/$uf"
        fail "sorry-in-user-file"
    fi
done

# GATE B (was step 4.6). Axiom/macro-declaration lint on the USER's
# files. This is the gate that bans `run_cmd` and every other escape
# hatch into environment mutation — which is exactly why it must
# precede the first elaboration rather than follow it.
for uf in proof.lean completed.lean; do
    if [ -f "$STAGE/$uf" ]; then
        lint_out=$(LC_ALL=C awk -f "$(cd "$(dirname "$0")" && pwd)/proof-source-lint.awk" \
                     "$STAGE/$uf" 2>&1) && lint_rc=0 || lint_rc=$?
        bad_decl=$(printf '%s' "$lint_out" | sed "s|$STAGE/||g")
        if [ "$lint_rc" -ne 0 ] || [ -n "$bad_decl" ]; then
            echo "$bad_decl"
            fail "axiom-or-macro-decl-in-user-file"
        fi
    fi
done

# On the completed path the caller stages the user's outline as
# Emitted.lean too, so the bytes step 1 is about to elaborate have now
# been linted. Assert that rather than leaving it to the reader: if a
# future caller change breaks the correspondence, this fails loudly
# instead of silently reopening B1.
if [ -f "$STAGE/completed.lean" ] && [ -f "$STAGE/Emitted.lean" ]; then
    if [ "$(digest "$STAGE/completed.lean")" != "$(digest "$STAGE/Emitted.lean")" ]; then
        fail "completed-path-emitted-not-linted"
    fi
fi

# Non-degradable timeout guard (seventh-audit amendment 2): the CI
# wrapper degrades to unguarded when coreutils is absent; the trust
# kernel refuses instead.
if command -v timeout >/dev/null 2>&1; then TO=(timeout 120)
elif command -v gtimeout >/dev/null 2>&1; then TO=(gtimeout 120)
else fail "no-timeout-guard"
fi

# Cleared environment: ambient LEAN_PATH is dropped, replaced by the
# stage dir only; `lake env` supplies the pinned project library.
run_lean() {
    ( cd "$PROJ" && env LEAN_PATH="$STAGE" "${TO[@]}" lake env lean "$@" ) 2>&1
}

# 0. Pinned support library must build.
build_out=$( ( cd "$PROJ" && "${TO[@]}" lake build ) 2>&1 ) || {
    echo "$build_out"; fail "support-library-build"; }

# 1. Emitted goal compiles.
# B1: first Lean action of the whole check. The text gates have run;
# assert the bytes about to be elaborated are still the ones they saw.
verify_unchanged Emitted.lean
emit_out=$(run_lean -o "$STAGE/Emitted.olean" "$STAGE/Emitted.lean") || {
    echo "$emit_out"; fail "emitted-does-not-compile"; }

# 2. Placeholder policy: every sorry in the emitted goal must be one
# of the two sanctioned in-statement forms (obligation binder /
# dead bounds fallback). The trailing goal_holds stub must have been
# stripped by the caller; anything else is unsanctioned.
bad_sorry=$(grep -n 'sorry' "$STAGE/Emitted.lean" \
    | grep -vE ': \(h_[A-Za-z0-9_]*obligation_\) := \(\(by sorry\)\);' \
    | grep -vF '| skip); all_goals sorry));' || true)
[ -z "$bad_sorry" ] || { echo "$bad_sorry"; fail "unsanctioned-sorry-in-emitted"; }

# Goal-presence is decided by the AUTHORITY, never by user-supplied
# content (R-1 fix, 2026-07-24 audit). On the completed-outline path
# the staged Emitted.lean IS the user's completed file (the caller
# overwrites it), so reading goal-presence from it let a completed
# outline without a bare `def goal :` line silently set
# has_goal_def=0 and disable the closer↔goal binding gate — admitting
# a closer that proves only `True`. The authority is the fresh
# emission: Generated.lean on the completed path, Emitted.lean
# (which IS the fresh emission) otherwise. The replay path always
# emits exactly one `def goal`, so on the completed path both a
# goal-less authority and a goal-less completed outline are hard
# failures, never a silent branch.
#
# C1 CATEGORY CLOSURE (2026-07-24, second audit finding A-2): the R-1
# fix hard-failed the COMPLETED path but left the plain path as a
# silent `has_goal_def=0` branch — and the same justification covers
# both. A goal rendered `noncomputable def goal.{u0} :` (which the
# emitter DOES produce: a `sort k≥1` anywhere in the term allocates a
# universe variable, and nothing refuses that today) misses this
# regex, and every downstream gate keyed on has_goal_def then
# silently disappeared — verified end-to-end: a proof.lean reading
# only `theorem totally_unrelated : 1+1=2 := rfl` was admitted.
#
# The rule this file now obeys, without exception: a recognizer that
# cannot answer must FAIL, never skip the gate it guards. So
# goal-presence is an INVARIANT here (asserted immediately below),
# not a flag consulted by later branches.
goal_def_re='^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goal[[:space:]]*:'
# Diagnose the known near-miss specifically, so the failure names the
# cause instead of leaving the next reader to rediscover A-2/A-9.
univ_goal_re='^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goal\.\{'
diagnose_missing_goal_def() {
    local f="$1" which="$2"
    if grep -qE "$univ_goal_re" "$f"; then
        grep -nE "$univ_goal_re" "$f" | sed "s|$STAGE/||g"
        echo "The $which emission carries UNIVERSE PARAMETERS. Replay cannot"
        echo "bind a universe-parameterized goal: the goal_holds stub drops the"
        echo "binders and proves it at one level only (audit A-9). Refuse the"
        echo "emission upstream rather than discharging it here."
    fi
}
if [ -f "$STAGE/completed.lean" ]; then
    [ -f "$STAGE/Generated.lean" ] || fail "completed-without-generated-reference"
    grep -qE "$goal_def_re" "$STAGE/Generated.lean" || {
        diagnose_missing_goal_def "$STAGE/Generated.lean" "authority"
        fail "authority-missing-goal-def"; }
    grep -qE "$goal_def_re" "$STAGE/Emitted.lean" \
        || fail "completed-outline-missing-goal-def"
else
    grep -qE "$goal_def_re" "$STAGE/Emitted.lean" || {
        diagnose_missing_goal_def "$STAGE/Emitted.lean" "fresh"
        fail "replay-emission-missing-goal-def"; }
fi
# From here on this is an INVARIANT, not a condition. Every gate below
# runs unconditionally; there is no has_goal_def flag to be 0.

# The GeneratedHarness namespace exists only in checker-staged probe
# files; user files have no legitimate mention of it, and a def
# planted inside it is exactly the R-1 capture shape (a user def the
# drift probe could resolve instead of the reference). Reject on
# sight, both paths.
for uf in proof.lean completed.lean; do
    if [ -f "$STAGE/$uf" ] && grep -qn 'GeneratedHarness' "$STAGE/$uf"; then
        grep -n 'GeneratedHarness' "$STAGE/$uf" | sed "s|$STAGE/||g"
        fail "harness-namespace-in-user-file"
    fi
done

# 3. Anti-trivialization (seventh-audit amendment 1): a goal the
# emission pipeline has trivialized closes by rfl/trivial; reject.
# (Genuinely trivial user goals are also rejected — loud, and SMT
# handles those; the pin guards the goal-formation layer.)
printf 'import Emitted\nexample : goal := by first | rfl | trivial\n' \
    > "$STAGE/triviality-probe.lean"
if run_lean "$STAGE/triviality-probe.lean" >/dev/null 2>&1; then
    fail "goal-formation-trivial"
fi

# 4. Completed-outline drift (when staged): the completed goal must
# be definitionally the generated goal. The completed path guarantees
# has_goal_def=1 (enforced above), so the probe is a fixed literal
# comparing the reference goal to the user's goal by rfl. (A former
# per-def branch for goal-less completed files was the R-1 hole: its
# awk read namespaces from the ALREADY-WRAPPED Generated.lean,
# producing a doubled-namespace LHS a user def could satisfy. Removed
# 2026-07-24 — the trust kernel has no goal-less completed path.)
if [ -f "$STAGE/completed.lean" ]; then
    # B1: Generated.lean is the AUTHORITY this check compares against —
    # the only thing binding the user's `def goal` to the SAW
    # obligation. It is also the file a metaprogram would rewrite to
    # make a substituted goal pass. Re-verify both sides against their
    # staged digests before compiling either.
    verify_unchanged Generated.lean
    verify_unchanged completed.lean
    gen_out=$(run_lean -o "$STAGE/Generated.olean" "$STAGE/Generated.lean") || {
        echo "$gen_out"; fail "generated-reference-does-not-compile"; }
    {
        echo "import Generated"
        echo "import Emitted"
        echo
        echo "#check (show GeneratedHarness.goal = goal from rfl)"
    } > "$STAGE/drift-check.lean"
    if ! drift_out=$(run_lean "$STAGE/drift-check.lean") \
       || printf '%s\n' "$drift_out" | grep -qE '^[^[:space:]]+: error'; then
        echo "$drift_out"; fail "completed-outline-drift"
    fi
fi

# 4.5 Sorry scan on the USER's files: zero tolerance (the axiom audit
# would catch a live sorry anyway via sorryAx — this fails faster and
# names the check the design specifies).
#
# A-10 (audit-2), RECONCILED 2026-07-25 in favour of zero tolerance.
# This rule and the placeholder policy at step 2 contradict each other
# on the completed-outline path, where they apply to the SAME BYTES:
# step 2 EXEMPTS the two sanctioned in-statement forms because they
# are generator output, while this rule forbids every `sorry` because
# the file is user input. On the completed path `completed.lean` is
# both, and the stricter rule wins.
#
# That is deliberate, not an oversight. The divergence is
# FAIL-CLOSED — it can only refuse a discharge, never admit one — so
# it costs completeness, not soundness, and the cheap "fix" (exempt
# the sanctioned forms here too) would trade a zero-tolerance rule
# for convenience. A completed outline that still contains `by sorry`
# has not discharged the obligation the placeholder stands for; the
# user is meant to REPLACE it, and when they do, nothing here fires.
#
# The residual case is real: a goal whose emitted form carries an
# obligation placeholder the user cannot discharge (e.g. the
# `H_prod` placeholder in `fix_classF_eval`) simply cannot go through
# the completed path. That is an EMITTER problem — the emitter should
# not produce an obligation it has no route to discharge — and it is
# filed as such in TODO.md rather than papered over here.
# MOVED to GATE A above (B1, 2026-07-29) — it now runs BEFORE the
# first elaboration. Re-run here, over bytes first re-verified against
# their staged digests, so that (a) the pre-elaboration result cannot
# have been invalidated by anything that ran since, and (b) deleting
# the moved copy by mistake still leaves a gate in the path.
verify_unchanged proof.lean
verify_unchanged completed.lean
for uf in proof.lean completed.lean; do
    if [ -f "$STAGE/$uf" ] && grep -qn 'sorry' "$STAGE/$uf"; then
        grep -n 'sorry' "$STAGE/$uf"
        fail "sorry-in-user-file"
    fi
done

# 4.6 Axiom-declaration lint on the USER's files (2026-07-21,
# introduced with the trust tiers; applies to ALL checks): proof-side
# files must never DECLARE axioms or reach machinery that can add
# declarations. The strict allowlist is exact-name so a hand-declared
# axiom cannot collide with it, but the native-eval tier admits a
# NAME PATTERN (declaration-dependent bv_decide axiom names) that a
# hand-declared axiom of a matching name could satisfy — a `private
# axiom` name even prints UNMANGLED in `#print axioms`. The shared
# lexer-based token lint (proof-source-lint.awk, single authority
# with the CI harness) tracks comments AND string/char literals
# (F1 fix — a comment-stripper without string awareness was blinded
# by a string containing the comment-open sequence) and bans every
# known escape hatch into environment mutation or kernel bypass.
# (The per-call-unique stage path is stripped from the lint output so
# the diagnostic is deterministic — driver goldens pin it.)
# LC_ALL=C: the lint is a byte-level lexer (its non-ASCII taint rule
# assumes byte mode), and UTF-8-locale awk can HARD-ERROR on some
# multibyte input. A nonzero awk exit must reject even with empty
# output — an awk crash must never read as a lint pass (F1-fix
# hardening, 2026-07-21).
# MOVED to GATE B above (B1, 2026-07-29). Re-run over re-verified
# bytes, for the same two reasons as the sorry scan.
for uf in proof.lean completed.lean; do
    if [ -f "$STAGE/$uf" ]; then
        lint_out=$(LC_ALL=C awk -f "$(cd "$(dirname "$0")" && pwd)/proof-source-lint.awk" \
                     "$STAGE/$uf" 2>&1) && lint_rc=0 || lint_rc=$?
        bad_decl=$(printf '%s' "$lint_out" | sed "s|$STAGE/||g")
        if [ "$lint_rc" -ne 0 ] || [ -n "$bad_decl" ]; then
            echo "$bad_decl"
            fail "axiom-or-macro-decl-in-user-file"
        fi
    fi
done

# 5. The user's proof elaborates.
proof_out=$(run_lean "$STAGE/proof.lean") || {
    echo "$proof_out"; fail "proof-does-not-elaborate"; }
if printf '%s\n' "$proof_out" | grep -qE '^[^[:space:]]+: error'; then
    echo "$proof_out"; fail "proof-does-not-elaborate"
fi

# 6. Closer contract: named theorems only; goal_closed of exactly the
# goal's type when a def goal exists.
closers=$(awk '
  /^[[:space:]]*(theorem|lemma)[[:space:]]+/ {
    name = $2
    sub(/:.*/, "", name)
    if (name != "") print name
  }
' "$STAGE/proof.lean")
[ -n "$closers" ] || fail "no-named-closer"
# UNCONDITIONAL (C1 closure): goal presence is an invariant above, so
# the binding gate has no skip branch. Previously guarded by
# `if [ "$has_goal_def" -eq 1 ]`, which is exactly how A-2 turned the
# whole gate off.
printf '%s\n' "$closers" | grep -qx 'goal_closed' || fail "missing-goal_closed"
# proof.lean is not a module name; compile it to an olean under a
# module-safe name instead.
cp "$STAGE/proof.lean" "$STAGE/UserProof.lean"
up_out=$(run_lean -o "$STAGE/UserProof.olean" "$STAGE/UserProof.lean") || {
    echo "$up_out"; fail "proof-does-not-elaborate"; }
# The binding is a KERNEL-CHECKED DECLARATION, not a `#check`
# (A-5 fix, 2026-07-24 second audit; RK-9 structurally).
#
# `#check (goal_closed : goal)` was decided by the ELABORATOR alone:
# `#check` adds no declaration, so nothing was ever kernel-checked,
# and a type ascription inserts COERCIONS. A user could supply
#     def hidden : goal := by ... native_decide
#     theorem goal_closed : True := trivial
#     instance : CoeT True goal_closed goal := ⟨hidden⟩
# whereupon the probe printed `hidden : goal` and passed — while the
# audit inspected `goal_closed` (clean) and never saw `hidden`'s
# native-evaluation axiom. That admitted compiler-level trust onto a
# row whose evidence record says STRICT tier.
#
# Declaring `__replay_binding : goal := goal_closed` fixes both
# halves: the kernel checks it, and it becomes an audited constant,
# so ANY axiom reachable through the real proof term — including one
# reached via an inserted coercion — is caught by the allowlist in
# step 7. The name is prefixed to keep it out of the user's way; a
# user file that declares it collides and fails to compile.
printf 'import Emitted\nimport UserProof\ntheorem __replay_binding : goal := goal_closed\n' \
    > "$STAGE/BindingProbe.lean"
bind_out=$(run_lean -o "$STAGE/BindingProbe.olean" "$STAGE/BindingProbe.lean")
bind_rc=$?
if [ "$bind_rc" -ne 0 ] \
   || printf '%s\n' "$bind_out" | grep -qE '^[^[:space:]]+: error'; then
    echo "$bind_out"; fail "closer-wrong-type"
fi

# 7. Axiom audit: every named closer, fixed allowlist.
if [ ! -f "$STAGE/UserProof.olean" ]; then
    cp "$STAGE/proof.lean" "$STAGE/UserProof.lean"
    up2_out=$(run_lean -o "$STAGE/UserProof.olean" "$STAGE/UserProof.lean") || {
        echo "$up2_out"; fail "proof-does-not-elaborate"; }
fi
# The BINDING CONSTANT is audited alongside the user's closers
# (A-5 fix): it is the only constant guaranteed to have the goal's
# type, so auditing it is what catches an axiom reached through an
# inserted coercion — the closer itself can be clean while the term
# actually proving the goal is not. `__replay_binding` is listed
# FIRST so the vacuity count below covers it too.
audited="__replay_binding
$closers"
{
    echo "import Emitted"
    echo "import UserProof"
    echo "import BindingProbe"
    # The allowlist matches EXACT fully qualified names. This probe
    # has no `open` commands, so names already print fully qualified;
    # the option makes that premise mechanical rather than incidental
    # (defense-in-depth, 2026-07-19).
    echo "set_option pp.fullNames true"
    printf '%s\n' "$audited" | while read -r nm; do
        echo "#print axioms $nm"
    done
} > "$STAGE/axiom-probe.lean"
ax_out=$(run_lean "$STAGE/axiom-probe.lean") || { echo "$ax_out"; fail "axiom-audit-run"; }
# Structured parse of "‘X’ depends on axioms: [...]" including
# multi-line bracket lists (same continuation handling as the CI
# harness's audit_axioms): reject any non-allowlisted entry.
#
# C3 (category closure, 2026-07-24): a nonzero awk exit must REJECT
# even with empty output. Testing only emptiness makes an awk
# hard-error read as a clean audit — the identical fail-open the F1
# fix hardened at the lint call site (:212-218) and did not
# generalize. Rule for the whole trust path: every subprocess
# capture checks exit status AND output.
bad_ax=$(printf '%s\n' "$ax_out" \
    | LC_ALL=C awk -v tier="$TRUST_TIER" -f "$(cd "$(dirname "$0")" && pwd)/axiom-audit.awk") \
    && ax_rc=0 || ax_rc=$?
if [ "$ax_rc" -ne 0 ] || [ -n "$bad_ax" ]; then
    echo "$bad_ax"
    [ "$ax_rc" -eq 0 ] || echo "(axiom-audit awk exited $ax_rc)"
    fail "axiom-outside-allowlist"
fi
# Vacuity guard (2026-07-20): the allowlist audit passes when it
# finds nothing to reject, so an audit that never RAN must not look
# like a pass. Every named closer must produce exactly one audited
# line ("depends on axioms" / "does not depend on any axioms");
# message-format drift or a silent probe fails loudly here.
n_closers=$(printf '%s\n' "$audited" | grep -c .)
n_audited=$(printf '%s\n' "$ax_out" \
    | grep -cE "depends on axioms|does not depend on any axioms")
[ "$n_audited" -eq "$n_closers" ] || {
    echo "$ax_out"
    echo "expected $n_closers audited closer(s), saw $n_audited audit line(s)"
    fail "axiom-audit-vacuous"; }
printf '%s\n' "$ax_out" | grep -E "depends on axioms|does not depend" \
    | sed 's/^/CHECK-AXIOMS: /'

echo "CHECK-OK"
exit 0
