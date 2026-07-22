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
#   axiom-decl-lint — proof.lean DECLARING an axiom (forging the
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
# even with a valid marker (this is the forgery defense: a
# hand-declared axiom matching the tier's name pattern must never
# reach the audit).
mkdir -p "$STAGE/axiom-decl-lint"
cat > "$STAGE/axiom-decl-lint/proof.lean" <<'EOF'
axiom forged._native.bv_decide.ax_1 : False
theorem tier_selftest_forged : False := forged._native.bv_decide.ax_1
EOF
printf 'native-eval\n' > "$STAGE/axiom-decl-lint/.trust-tier"
run_case axiom-decl-lint "axiom/macro declaration in proof-side file"

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
# Suffix-named impostor rejected under BOTH tiers (review-finding pin).
awk_case suffix-strict "" "cheat_vecToBitVec_bitVecToVec" reject
awk_case suffix-tier "native-eval" "cheat_vecToBitVec_bitVecToVec, p._native.bv_decide.ax_1" reject
# Prefix-named impostor rejected.
awk_case prefix-strict "" "propext_evil" reject
# bv_decide native axioms rejected under STRICT (tier gate is real).
awk_case native-strict "" "p._native.bv_decide.ax_1_10" reject
# sorryAx rejected even under the tier.
awk_case sorry-tier "native-eval" "sorryAx, p._native.bv_decide.ax_1" reject
# Forged near-miss of the tier pattern rejected under the tier
# (missing ax_ suffix / wrong family).
awk_case forged-family "native-eval" "p._native.native_decide.ax_1, p._native.bv_decide.ax_1" reject

if [ "$status" -eq 0 ]; then
    echo "trust-tier-selftest: ALL CASES OK"
fi
exit $status
