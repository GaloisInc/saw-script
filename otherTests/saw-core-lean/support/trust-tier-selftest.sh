#!/usr/bin/env bash
# Trust-tier guard self-test (2026-07-21, introduced with the
# native-eval tier). Mutation tests for the tier machinery in
# lean-proof-test.sh + replay/axiom-audit.awk: each case stages a
# synthetic row that MUST FAIL with a specific diagnostic. A guard
# that stops firing is a silent trust hole (vacuity-guard doctrine:
# every guard ships with a mutation it demonstrably catches).
#
# Cases:
#   stale-marker    — .trust-tier on a row whose proof uses no
#                     bv_decide native axiom => TRUST-TIER-UNUSED.
#   unknown-tier    — .trust-tier naming an unrecognized tier
#                     => UNKNOWN-TRUST-TIER.
#   missing-marker  — bv_decide proof WITHOUT .trust-tier => the
#                     per-invocation native axiom is rejected by the
#                     strict allowlist.
#   axiom-decl-lint — proof.lean DECLARING an axiom (colliding with the
#                     tier's name pattern) => source lint failure,
#                     regardless of marker.
#
# Invoked by test.sh (conformance and default test verbs). Stages
# rows under ../.tier-selftest/<case>/ so relative paths match real
# category rows; the staging dir is removed on every exit path.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
CATROOT="$(cd "$HERE/.." && pwd)"
STAGE="$CATROOT/.tier-selftest"

VERB="${1:-test}"
case "$VERB" in
    good) echo "trust-tier-selftest.sh: 'good' is a no-op"; exit 0 ;;
    clean) rm -rf "$STAGE"; exit 0 ;;
    test) ;;
    *) echo "trust-tier-selftest.sh: unknown verb '$VERB'" >&2; exit 1 ;;
esac

rm -rf "$STAGE"
mkdir -p "$STAGE"
trap 'rm -rf "$STAGE"' EXIT

status=0

# run_case <name> <required-diagnostic-substring>
# The synthetic row is expected to have been staged at $STAGE/<name>.
run_case() {
    local name="$1" want="$2" out rc
    out=$( cd "$STAGE/$name" && bash "$HERE/lean-proof-test.sh" test 2>&1 )
    rc=$?
    if [ "$rc" -eq 0 ]; then
        echo "FAIL[$name]: harness PASSED a row the tier guards must reject"
        echo "$out" | tail -5
        status=1
    elif ! printf '%s\n' "$out" | grep -qF "$want"; then
        echo "FAIL[$name]: harness failed, but WITHOUT the required diagnostic '$want'"
        echo "$out" | tail -10
        status=1
    else
        echo "OK[$name]: rejected with '$want'"
    fi
}

# Case 1: stale marker — tier declared, proof needs no tier axiom.
mkdir -p "$STAGE/stale-marker"
printf 'theorem tier_selftest_trivial : True := trivial\n' \
    > "$STAGE/stale-marker/proof.lean"
printf 'native-eval\n' > "$STAGE/stale-marker/.trust-tier"
run_case stale-marker "TRUST-TIER-UNUSED"

# Case 2: unknown tier name.
mkdir -p "$STAGE/unknown-tier"
printf 'theorem tier_selftest_trivial : True := trivial\n' \
    > "$STAGE/unknown-tier/proof.lean"
printf 'super-trusting\n' > "$STAGE/unknown-tier/.trust-tier"
run_case unknown-tier "UNKNOWN-TRUST-TIER"

# Case 3: bv_decide without a marker — strict allowlist must reject
# the per-invocation native axiom. The goal must actually reach the
# SAT/LRAT path (bv_normalize alone closes trivialities like
# x ^^^ x = 0 WITHOUT a native axiom — verified 2026-07-21);
# multiplication commutativity bitblasts for real.
mkdir -p "$STAGE/missing-marker"
cat > "$STAGE/missing-marker/proof.lean" <<'EOF'
import Std.Tactic.BVDecide
theorem tier_selftest_bv (x y : BitVec 8) : x * y = y * x := by bv_decide
EOF
run_case missing-marker "._native.bv_decide.ax_"

# Case 4: axiom declaration in a proof-side file — source lint fires
# even with a valid marker (this is the name-collision defense: a
# hand-declared axiom matching the tier's name pattern must never
# reach the audit).
mkdir -p "$STAGE/axiom-decl-lint"
cat > "$STAGE/axiom-decl-lint/proof.lean" <<'EOF'
axiom collide._native.bv_decide.ax_1 : False
theorem tier_selftest_collide : False := collide._native.bv_decide.ax_1
EOF
printf 'native-eval\n' > "$STAGE/axiom-decl-lint/.trust-tier"
run_case axiom-decl-lint "axiom/macro declaration in proof-side file"

# Case 5 (2026-07-21 hardening pin): `private axiom` — the modifier
# prefix bypassed the original line-anchored lint, and a private
# axiom's name prints UNMANGLED in `#print axioms`, so before the
# hardening this matching-named axiom would have been ADMITTED on a tier row. The
# comment-aware token lint must reject it.
mkdir -p "$STAGE/private-axiom-decl"
cat > "$STAGE/private-axiom-decl/proof.lean" <<'EOF'
private axiom goal_holds._native.bv_decide.ax_1 : False
theorem tier_selftest_priv : False := goal_holds._native.bv_decide.ax_1
EOF
printf 'native-eval\n' > "$STAGE/private-axiom-decl/.trust-tier"
run_case private-axiom-decl "axiom/macro declaration in proof-side file"

# Case 6 (2026-07-21 hardening pin): `set_option … in axiom` — a
# command prefix on the same line also bypassed the original lint.
mkdir -p "$STAGE/prefixed-axiom-decl"
cat > "$STAGE/prefixed-axiom-decl/proof.lean" <<'EOF'
set_option pp.fullNames true in axiom goal_closed._native.bv_decide.ax_1 : False
theorem tier_selftest_pref : False := goal_closed._native.bv_decide.ax_1
EOF
printf 'native-eval\n' > "$STAGE/prefixed-axiom-decl/.trust-tier"
run_case prefixed-axiom-decl "axiom/macro declaration in proof-side file"

# --- Pure-awk allowlist cases -------------------------------------
# The audit layer's own rejection semantics, exercised directly on
# synthetic `#print axioms` output (no Lean involved). These carry the
# exact-vs-suffix discipline pin at the layer that owns it: the
# end-to-end replay rows (saw-boundary/replay_reject_axiom,
# replay_reject_suffix_axiom) now fire at the earlier source-lint
# layer, so the awk's own discipline must be pinned here.

AWK_AUDIT="$(cd "$CATROOT/../../saw-core-lean/replay" && pwd)/axiom-audit.awk"

# awk_case <name> <tier> <axioms-csv> <want> ; want = "reject" | "pass"
awk_case() {
    local name="$1" tier="$2" axioms="$3" want="$4" out
    out=$(printf "'p' depends on axioms: [%s]\n" "$axioms" \
          | awk -v tier="$tier" -f "$AWK_AUDIT")
    case "$want" in
        reject)
            if [ -z "$out" ]; then
                echo "FAIL[awk:$name]: allowlist ACCEPTED axioms it must reject: $axioms (tier='$tier')"
                status=1
            else
                echo "OK[awk:$name]"
            fi ;;
        pass)
            if [ -n "$out" ]; then
                echo "FAIL[awk:$name]: allowlist rejected allowlisted axioms: $out"
                status=1
            else
                echo "OK[awk:$name]"
            fi ;;
    esac
}

# Exact allowlist accepted (strict).
awk_case exact-accept "" "propext, Classical.choice, Quot.sound, CryptolToLean.SAWCorePrimitives.vecToBitVec_bitVecToVec" pass
# The GENUINE tier shape accepted under the tier (goal_holds/goal_closed
# closers only — 2026-07-21 prefix pinning).
awk_case tier-accept "native-eval" "propext, goal_holds._native.bv_decide.ax_1_10, goal_closed._native.bv_decide.ax_2_5" pass
# Suffix-named look-alike rejected under BOTH tiers (review-finding pin).
awk_case suffix-strict "" "cheat_vecToBitVec_bitVecToVec" reject
awk_case suffix-tier "native-eval" "cheat_vecToBitVec_bitVecToVec, goal_holds._native.bv_decide.ax_1" reject
# Prefix-named look-alike rejected.
awk_case prefix-strict "" "propext_evil" reject
# bv_decide native axioms rejected under STRICT (tier gate is real).
awk_case native-strict "" "goal_holds._native.bv_decide.ax_1_10" reject
# sorryAx rejected even under the tier.
awk_case sorry-tier "native-eval" "sorryAx, goal_holds._native.bv_decide.ax_1" reject
# Non-canonical near-misses of the tier pattern rejected under the tier:
# wrong tactic family, and a non-sanctioned declaration prefix (the
# 2026-07-21 confirmed matching-name case — a private axiom named
# evil._native.bv_decide.ax_1 prints unmangled and matched the
# pre-hardening wildcard-prefix pattern).
awk_case noncanonical-family "native-eval" "goal_holds._native.native_decide.ax_1, goal_holds._native.bv_decide.ax_1" reject
awk_case noncanonical-prefix "native-eval" "evil._native.bv_decide.ax_1, goal_holds._native.bv_decide.ax_1" reject

if [ "$status" -eq 0 ]; then
    echo "trust-tier-selftest: ALL CASES OK"
fi
exit $status
