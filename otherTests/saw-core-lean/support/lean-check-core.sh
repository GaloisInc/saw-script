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
#   lean-check-core.sh <lean-project-root-abs> <stage-dir-abs>
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
#                      GeneratedHarness) for the drift check
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

fail() { echo "CHECK-FAIL: $1"; exit 1; }

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
if command -v timeout >/dev/null 2>&1; then TO="timeout 120"
elif command -v gtimeout >/dev/null 2>&1; then TO="gtimeout 120"
else fail "no-timeout-guard"
fi

# Cleared environment: ambient LEAN_PATH is dropped, replaced by the
# stage dir only; `lake env` supplies the pinned project library.
run_lean() {
    ( cd "$PROJ" && env LEAN_PATH="$STAGE" $TO lake env lean "$@" ) 2>&1
}

# 0. Pinned support library must build.
build_out=$( ( cd "$PROJ" && $TO lake build ) 2>&1 ) || {
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

has_goal_def=0
if grep -qE '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goal[[:space:]]*:' "$STAGE/Emitted.lean"; then
    has_goal_def=1
fi

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

# 4. Completed-outline drift (when staged): the completed goal must be
# definitionally the generated goal; per-def form for module
# artifacts; the check file must be non-vacuous.
if [ -f "$STAGE/completed.lean" ]; then
    [ -f "$STAGE/Generated.lean" ] || fail "completed-without-generated-reference"
    gen_out=$(run_lean -o "$STAGE/Generated.olean" "$STAGE/Generated.lean") || {
        echo "$gen_out"; fail "generated-reference-does-not-compile"; }
    {
        echo "import Generated"
        echo "import Emitted"
        echo
        if [ "$has_goal_def" -eq 1 ]; then
            echo "#check (show GeneratedHarness.goal = goal from rfl)"
        else
            awk '
              /^[[:space:]]*namespace[[:space:]]+/ { ns = $2; next }
              /^[[:space:]]*end[[:space:]]+/ { ns = ""; next }
              /^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+/ {
                name = ""
                for (i = 1; i <= NF; i++) if ($i == "def") { name = $(i+1); break }
                sub(/[:(].*/, "", name)
                if (name != "") {
                  q = (ns != "" ? ns "." name : name)
                  print "#check (show GeneratedHarness." q " = " q " from rfl)"
                }
              }
            ' "$STAGE/Generated.lean"
        fi
    } > "$STAGE/drift-check.lean"
    grep -q '^#check' "$STAGE/drift-check.lean" || fail "vacuous-drift-check"
    drift_out=$(run_lean "$STAGE/drift-check.lean")
    if [ $? -ne 0 ] || printf '%s\n' "$drift_out" | grep -qE '^[^[:space:]]+: error'; then
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
    ct_out=$(run_lean "$STAGE/closer-type-probe.lean")
    if [ $? -ne 0 ] || printf '%s\n' "$ct_out" | grep -qE '^[^[:space:]]+: error'; then
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
    printf '%s\n' "$closers" | while read -r nm; do
        echo "#print axioms $nm"
    done
} > "$STAGE/axiom-probe.lean"
ax_out=$(run_lean "$STAGE/axiom-probe.lean") || { echo "$ax_out"; fail "axiom-audit-run"; }
# Structured parse of "‘X’ depends on axioms: [...]" including
# multi-line bracket lists (same continuation handling as the CI
# harness's audit_axioms): reject any non-allowlisted entry.
bad_ax=$(printf '%s\n' "$ax_out" | awk '
  function check(line,    n, xs, i, ax) {
    sub(/^.*depends on axioms: \[/, "", line)
    sub(/\].*$/, "", line)
    n = split(line, xs, /,[[:space:]]*/)
    for (i = 1; i <= n; i++) {
      ax = xs[i]
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", ax)
      # EXACT match against the fixed allowlist — never suffix/regex.
      # A suffix match would admit a user axiom named e.g.
      # unsound_vecToBitVec_bitVecToVec (review finding, an unsoundness
      # hole). Both the qualified and short spellings #print axioms
      # may report are enumerated, matching the CI harness exactly
      # (lean-proof-test.sh audit_axioms) — the single-checker
      # principle requires identical allowlist semantics.
      if (ax != "" &&
          ax != "propext" &&
          ax != "Classical.choice" &&
          ax != "Quot.sound" &&
          ax != "CryptolToLean.SAWCorePrimitives.vecToBitVec_bitVecToVec" &&
          ax != "CryptolToLean.SAWCorePrimitives.bitVecToVec_vecToBitVec" &&
          ax != "vecToBitVec_bitVecToVec" &&
          ax != "bitVecToVec_vecToBitVec") print ax
    }
  }
  /depends on axioms:/ {
    pending = $0
    if (pending ~ /\]/) { check(pending); pending = "" }
    else collecting = 1
    next
  }
  collecting {
    pending = pending " " $0
    if ($0 ~ /\]/) { check(pending); pending = ""; collecting = 0 }
  }')
[ -z "$bad_ax" ] || { echo "$bad_ax"; fail "axiom-outside-allowlist"; }
printf '%s\n' "$ax_out" | grep -E "depends on axioms|does not depend" \
    | sed 's/^/CHECK-AXIOMS: /'

echo "CHECK-OK"
exit 0
