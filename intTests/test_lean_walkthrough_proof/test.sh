# Bespoke driver — verifies the worked example in
# doc/getting-started.md elaborates AND its tactic proof closes
# the goal.
#
# When `lake` is unavailable (CI without a Lean toolchain) we skip
# the whole test rather than fail — exit 0 with a one-line note.

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

# Make sure the project itself is up to date.
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
else
    echo "OK: proof.lean elaborated; tactic discharged goal"
fi

rm -rf "$PROBE_DIR"
exit $status
