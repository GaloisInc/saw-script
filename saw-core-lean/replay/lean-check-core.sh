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
goal_def_re='^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goal[[:space:]]*:'
if [ -f "$STAGE/completed.lean" ]; then
    [ -f "$STAGE/Generated.lean" ] || fail "completed-without-generated-reference"
    grep -qE "$goal_def_re" "$STAGE/Generated.lean" \
        || fail "authority-missing-goal-def"
    grep -qE "$goal_def_re" "$STAGE/Emitted.lean" \
        || fail "completed-outline-missing-goal-def"
    has_goal_def=1
else
    has_goal_def=0
    if grep -qE "$goal_def_re" "$STAGE/Emitted.lean"; then
        has_goal_def=1
    fi
fi

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
if [ "$has_goal_def" -eq 1 ]; then
    printf 'import Emitted\nexample : goal := by first | rfl | trivial\n' \
        > "$STAGE/triviality-probe.lean"
    if run_lean "$STAGE/triviality-probe.lean" >/dev/null 2>&1; then
        fail "goal-formation-trivial"
    fi
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
if [ "$has_goal_def" -eq 1 ]; then
    printf '%s\n' "$closers" | grep -qx 'goal_closed' || fail "missing-goal_closed"
    printf 'import Emitted\nimport proof\n#check (goal_closed : goal)\n' \
        > "$STAGE/closer-type-probe.lean"
    # proof.lean is not a module name; compile it to an olean under a
    # module-safe name instead.
    cp "$STAGE/proof.lean" "$STAGE/UserProof.lean"
    up_out=$(run_lean -o "$STAGE/UserProof.olean" "$STAGE/UserProof.lean") || {
        echo "$up_out"; fail "proof-does-not-elaborate"; }
    printf 'import Emitted\nimport UserProof\n#check (goal_closed : goal)\n' \
        > "$STAGE/closer-type-probe.lean"
    if ! ct_out=$(run_lean "$STAGE/closer-type-probe.lean") \
       || printf '%s\n' "$ct_out" | grep -qE '^[^[:space:]]+: error'; then
        echo "$ct_out"; fail "closer-wrong-type"
    fi
fi

# 7. Axiom audit: every named closer, fixed allowlist.
if [ ! -f "$STAGE/UserProof.olean" ]; then
    cp "$STAGE/proof.lean" "$STAGE/UserProof.lean"
    up2_out=$(run_lean -o "$STAGE/UserProof.olean" "$STAGE/UserProof.lean") || {
        echo "$up2_out"; fail "proof-does-not-elaborate"; }
fi
{
    echo "import Emitted"
    echo "import UserProof"
    # The allowlist matches EXACT fully qualified names. This probe
    # has no `open` commands, so names already print fully qualified;
    # the option makes that premise mechanical rather than incidental
    # (defense-in-depth, 2026-07-19).
    echo "set_option pp.fullNames true"
    printf '%s\n' "$closers" | while read -r nm; do
        echo "#print axioms $nm"
    done
} > "$STAGE/axiom-probe.lean"
ax_out=$(run_lean "$STAGE/axiom-probe.lean") || { echo "$ax_out"; fail "axiom-audit-run"; }
# Structured parse of "‘X’ depends on axioms: [...]" including
# multi-line bracket lists (same continuation handling as the CI
# harness's audit_axioms): reject any non-allowlisted entry.
bad_ax=$(printf '%s\n' "$ax_out" \
    | awk -v tier="$TRUST_TIER" -f "$(cd "$(dirname "$0")" && pwd)/axiom-audit.awk")
[ -z "$bad_ax" ] || { echo "$bad_ax"; fail "axiom-outside-allowlist"; }
# Vacuity guard (2026-07-20): the allowlist audit passes when it
# finds nothing to reject, so an audit that never RAN must not look
# like a pass. Every named closer must produce exactly one audited
# line ("depends on axioms" / "does not depend on any axioms");
# message-format drift or a silent probe fails loudly here.
n_closers=$(printf '%s\n' "$closers" | grep -c .)
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
