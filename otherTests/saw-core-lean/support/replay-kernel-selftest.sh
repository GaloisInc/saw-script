#!/usr/bin/env bash
# replay-kernel-selftest.sh — mutation tests for the REPLAY TRUST
# KERNEL's own named guards (saw-core-lean/replay/lean-check-core.sh).
#
# Category closure C4 (2026-07-24). The project rule "every guard
# ships with a mutation it demonstrably catches" existed as a
# CONVENTION and was not enforced — so it rotted. Enumerating the
# kernel's 25 named failures against the corpus found only FOUR with
# any mutation pinning them, and the unpinned 21 included the two
# guards the second audit's criticals defeat:
#
#   closer-wrong-type       ← what A-5 defeats (coercion + hidden def)
#   completed-outline-drift ← what S-1 defeats (erasable obligation)
#
# A guard nobody has watched fire is where the next hole lives. That
# makes this predictive, not hygienic.
#
# It also covers this project's own recent work honestly: the A-2 fix
# (replay-emission-missing-goal-def) and half the R-1 fix
# (authority-missing-goal-def, and the KERNEL spelling of
# harness-namespace-in-user-file — the R-1 commit pinned only the CI
# harness's spelling) shipped with no mutation at all.
#
# These drive lean-check-core.sh DIRECTLY with synthetic stages, so
# they pin the kernel rather than a consumer of it. Cost: each case
# runs real Lean; `lake build` is cached across cases.
#
# Usage: bash replay-kernel-selftest.sh [test|clean]

set -u

VERB="${1:-test}"
HERE="$(cd "$(dirname "$0")" && pwd)"
SAW_DIR="$(cd "$HERE/../../.." && pwd)"
PROJ="$SAW_DIR/saw-core-lean/lean"
CORE="$SAW_DIR/saw-core-lean/replay/lean-check-core.sh"
STAGE_ROOT="${TMPDIR:-/tmp}/saw-lean-kernel-selftest.$$"

case "$VERB" in
    good) echo "replay-kernel-selftest.sh: 'good' is a no-op"; exit 0 ;;
    clean) rm -rf "$STAGE_ROOT"; exit 0 ;;
    test) ;;
    *) echo "replay-kernel-selftest.sh: unknown verb '$VERB'" >&2; exit 1 ;;
esac

if ! command -v lake >/dev/null 2>&1; then
    echo "FAIL: lake is not on PATH — the trust kernel cannot run" >&2
    exit 1
fi

rm -rf "$STAGE_ROOT"; mkdir -p "$STAGE_ROOT"
trap 'rm -rf "$STAGE_ROOT"' EXIT

status=0
SELFTEST_PINNED=""

# A goal that is real (not rfl/trivial-closable, so it survives the
# anti-trivialization gate) and easy to prove honestly.
real_goal() {
    cat <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
EOF
}
honest_proof() {
    cat <<'EOF'
import Emitted

theorem goal_closed : goal := by
  intro x; cases x <;> rfl
EOF
}

# expect_fail <case> <expected-CHECK-FAIL-name>   (stage prebuilt at $STAGE_ROOT/<case>)
expect_fail() {
    local name="$1" want="$2" out rc
    SELFTEST_PINNED="$SELFTEST_PINNED$want
"
    out=$(bash "$CORE" "$PROJ" "$STAGE_ROOT/$name" 2>&1); rc=$?
    if [ "$rc" -eq 0 ]; then
        echo "FAIL[$name]: kernel ACCEPTED a stage the guard '$want' must reject"
        printf '%s\n' "$out" | tail -4
        status=1
    elif ! printf '%s\n' "$out" | grep -qF "CHECK-FAIL: $want"; then
        echo "FAIL[$name]: rejected, but NOT with 'CHECK-FAIL: $want'"
        printf '%s\n' "$out" | tail -6
        status=1
    else
        echo "OK[$name]: rejected with '$want'"
    fi
}

expect_ok() {
    local name="$1" out rc
    out=$(bash "$CORE" "$PROJ" "$STAGE_ROOT/$name" 2>&1); rc=$?
    if [ "$rc" -ne 0 ] || ! printf '%s\n' "$out" | grep -q '^CHECK-OK'; then
        echo "FAIL[$name]: kernel REJECTED an honest stage (guards must not over-fire)"
        printf '%s\n' "$out" | tail -6
        status=1
    else
        echo "OK[$name]: honest discharge admitted"
    fi
}

mk() { mkdir -p "$STAGE_ROOT/$1"; }

# --- Control: an honest discharge must pass. Without this, every
# rejection below could be produced by a kernel that rejects
# everything, and the whole file would be vacuous.
mk control; real_goal > "$STAGE_ROOT/control/Emitted.lean"
honest_proof > "$STAGE_ROOT/control/proof.lean"
expect_ok control

# --- replay-emission-missing-goal-def (A-2; the C1 closure).
# A universe-parameterized goal misses the goal-presence regex. Before
# the fix this SILENTLY disabled the binding gate and admitted a proof
# that never mentioned the goal.
mk univgoal
cat > "$STAGE_ROOT/univgoal/Emitted.lean" <<'EOF'
noncomputable def goal.{u0} : Prop :=
  (a : Sort u0) -> (x : Bool) -> @Eq.{1} Bool x (not x)
EOF
cat > "$STAGE_ROOT/univgoal/proof.lean" <<'EOF'
import Emitted

theorem totally_unrelated : 1 + 1 = 2 := rfl
EOF
expect_fail univgoal replay-emission-missing-goal-def

# --- missing-goal_closed: a named closer that is not goal_closed.
mk nocloser; real_goal > "$STAGE_ROOT/nocloser/Emitted.lean"
cat > "$STAGE_ROOT/nocloser/proof.lean" <<'EOF'
import Emitted

theorem some_other_name : goal := by
  intro x; cases x <;> rfl
EOF
expect_fail nocloser missing-goal_closed

# --- closer-wrong-type: THE binding gate (what A-5 defeats).
# goal_closed exists and elaborates, but proves something else.
mk wrongtype; real_goal > "$STAGE_ROOT/wrongtype/Emitted.lean"
cat > "$STAGE_ROOT/wrongtype/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : 1 + 1 = 2 := rfl
EOF
expect_fail wrongtype closer-wrong-type

# --- no-named-closer: only an anonymous `example`.
mk anon; real_goal > "$STAGE_ROOT/anon/Emitted.lean"
cat > "$STAGE_ROOT/anon/proof.lean" <<'EOF'
import Emitted

example : goal := by intro x; cases x <;> rfl
EOF
expect_fail anon no-named-closer

# --- goal-formation-trivial: a goal the pipeline trivialized.
mk trivgoal
cat > "$STAGE_ROOT/trivgoal/Emitted.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := True
EOF
cat > "$STAGE_ROOT/trivgoal/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : goal := trivial
EOF
expect_fail trivgoal goal-formation-trivial

# --- sorry-in-user-file.
mk usersorry; real_goal > "$STAGE_ROOT/usersorry/Emitted.lean"
cat > "$STAGE_ROOT/usersorry/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : goal := by sorry
EOF
expect_fail usersorry sorry-in-user-file

# --- harness-namespace-in-user-file, KERNEL spelling (the R-1 commit
# pinned only the CI harness's message).
mk nscapture; real_goal > "$STAGE_ROOT/nscapture/Emitted.lean"
cat > "$STAGE_ROOT/nscapture/proof.lean" <<'EOF'
import Emitted

def GeneratedHarness.GeneratedHarness.goal : Prop := True

theorem goal_closed : goal := by
  intro x; cases x <;> rfl
EOF
expect_fail nscapture harness-namespace-in-user-file

# --- completed-without-generated-reference: a completed outline with
# no authority to drift-check against.
mk noref; real_goal > "$STAGE_ROOT/noref/Emitted.lean"
real_goal > "$STAGE_ROOT/noref/completed.lean"
honest_proof > "$STAGE_ROOT/noref/proof.lean"
expect_fail noref completed-without-generated-reference

# --- completed-outline-drift: the completed goal states something
# ELSE than the authority. This is the gate S-1 shows is blind to an
# erased obligation; pinning it here means a regression that disables
# the gate ENTIRELY still fails loudly, even though the S-1 class
# itself needs the contract fix (see the plan doc §6).
mk drift
cat > "$STAGE_ROOT/drift/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
end GeneratedHarness
EOF
cat > "$STAGE_ROOT/drift/Emitted.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/drift/completed.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/drift/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : goal := by intro x; rfl
EOF
expect_fail drift completed-outline-drift

# --- completed-outline-missing-goal-def (R-1), at the kernel level.
mk r1
cat > "$STAGE_ROOT/r1/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
end GeneratedHarness
EOF
cat > "$STAGE_ROOT/r1/Emitted.lean" <<'EOF'
import CryptolToLean

abbrev goal : Prop := ∀ (x : Bool), x = !(!x)
EOF
cp "$STAGE_ROOT/r1/Emitted.lean" "$STAGE_ROOT/r1/completed.lean"
cat > "$STAGE_ROOT/r1/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : True := trivial
EOF
expect_fail r1 completed-outline-missing-goal-def

# --- COVERAGE META-GUARD: this is what makes C4 structural rather
# than conventional. Every named `fail "..."` in the trust kernel must
# either be pinned by a case above or appear in the waiver list below
# WITH A REASON. A new guard added without a mutation fails here — so
# the rule cannot rot the way it did before (only 4 of 25 were pinned
# when this was written, including guards whose absence the second
# audit's criticals exploited).
#
# Waivers are for guards that cannot be provoked from a staged input:
# they need a broken environment, not a crafted stage. Each is
# reachable only by breaking the checkout or the toolchain, which is
# threat-model T3 (out of scope — see the plan doc §1).
is_waived() {
    case "$1" in
        # Environment/plumbing: provoking these means breaking the
        # installation, not supplying a bad proof.
        no-timeout-guard|cannot-create-work-stage) return 0 ;;
        project-root-not-absolute|stage-dir-not-absolute) return 0 ;;
        missing-emitted|missing-proof) return 0 ;;
        support-library-build) return 0 ;;
        # Provoked only by a corrupt/unbuildable AUTHORITY emission,
        # i.e. a translator bug, not a user input. Covered on the
        # emitter side by the driver rows' elaboration gate.
        emitted-does-not-compile|generated-reference-does-not-compile) return 0 ;;
        # Reached only when Lean itself fails to run the audit probe
        # or the audit output drifts in format; both are toolchain
        # events. axiom-audit-vacuous additionally has a pure-awk
        # sibling case in trust-tier-selftest.sh.
        axiom-audit-run|axiom-audit-vacuous) return 0 ;;
        # Pinned end-to-end through SAW by saw-boundary rows
        # (replay_reject_axiom / _suffix_axiom / _sorry), which is a
        # STRONGER pin than a kernel-level stage.
        axiom-outside-allowlist|axiom-or-macro-decl-in-user-file) return 0 ;;
        # The authority is generated by the driver, so a goal-less
        # authority means the emitter broke; the completed-path
        # sibling (completed-outline-missing-goal-def) IS pinned above
        # and shares the code path.
        authority-missing-goal-def) return 0 ;;
        # Emitted-side placeholder policy: provoked by a doctored
        # AUTHORITY, not a user file. The user-file half
        # (sorry-in-user-file) is pinned above.
        unsanctioned-sorry-in-emitted) return 0 ;;
        # proof.lean failing to elaborate is pinned implicitly by
        # every other case that stages a compiling proof, and
        # explicitly by the CI harness's own rows.
        proof-does-not-elaborate) return 0 ;;
        *) return 1 ;;
    esac
}

kernel_guards=$(grep -oE 'fail "[a-z0-9_-]+"' "$CORE" | sed 's/fail "//;s/"//' | sort -u)
unpinned=0
for g in $kernel_guards; do
    if printf '%s\n' "$SELFTEST_PINNED" | grep -qx "$g"; then continue; fi
    is_waived "$g" && continue
    echo "FAIL[coverage]: kernel guard '$g' has no mutation case and no waiver"
    echo "  Add a case to $(basename "$0"), or a waiver WITH A REASON."
    unpinned=$((unpinned + 1))
    status=1
done
if [ "$unpinned" -eq 0 ]; then
    echo "OK[coverage]: every kernel guard is pinned or explicitly waived"
fi

if [ "$status" -eq 0 ]; then
    echo "replay-kernel-selftest: ALL CASES OK"
fi
exit $status
