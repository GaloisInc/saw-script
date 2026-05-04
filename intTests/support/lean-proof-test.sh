# Shared harness for intTests/test_lean_*_proof/ directories.
#
# Each such directory contains a `proof.lean` file that should
# elaborate cleanly and contain no `sorry`. This script:
#   1. Skips if `lake` is unavailable (no Lean toolchain installed).
#   2. Runs `lake build` on the saw-core-lean library.
#   3. Copies proof.lean into a tmp probe directory under the lean
#      project, runs `lake env lean` against it.
#   4. Fails if elaboration errors, OR if elaboration succeeds but
#      uses `sorry` (which masks incomplete proofs).
#
# Each test dir's test.sh is a one-liner that delegates here:
#   exec ${TEST_SHELL:-bash} ../support/lean-proof-test.sh "$@"
#
# See intTests/test_lean_E1_bvAdd_comm_proof/ for the canonical
# layout (test.sh, Makefile, proof.lean, README).

set -u

if ! command -v lake >/dev/null 2>&1; then
    echo "lake unavailable; skipping (Lean-only test)"
    exit 0
fi

LAKE_DIR="$(cd ../../saw-core-lean/lean && pwd)"
TEST_NAME="$(basename "$(pwd)")"
PROBE_DIR="$LAKE_DIR/intTestsProbe/$TEST_NAME"

mkdir -p "$PROBE_DIR"
cp proof.lean "$PROBE_DIR/proof.lean"

# Make sure the project itself is up to date. If lake build fails
# (often: HOME overridden so elan can't find its toolchain), treat
# as a skip rather than a hard test failure — the build itself is
# covered by other CI paths.
build_log=$( ( cd "$LAKE_DIR" && lake build ) 2>&1 )
if [ $? -ne 0 ]; then
    echo "lake build failed for $LAKE_DIR; skipping (Lean-only test)"
    echo "$build_log"
    rm -rf "$PROBE_DIR"
    exit 0
fi

status=0

# proof.lean MUST elaborate cleanly.
proof_out=$( ( cd "$LAKE_DIR" && lake env lean \
                "intTestsProbe/$TEST_NAME/proof.lean" ) 2>&1 ) && \
    proof_rc=0 || proof_rc=$?
echo "--- proof.lean (expected: OK) ---"
echo "$proof_out"
echo "exit=$proof_rc"

if [ "$proof_rc" -ne 0 ] || echo "$proof_out" | grep -qE "^[^[:space:]]+: error" ; then
    echo "FAIL: proof.lean did not elaborate cleanly"
    status=1
elif echo "$proof_out" | grep -q "declaration uses \`sorry\`" ; then
    echo "FAIL: proof.lean elaborates but uses \`sorry\`"
    status=1
else
    echo "OK: proof.lean elaborated; tactic discharged goal"
fi

rm -rf "$PROBE_DIR"
exit $status
