# Bespoke driver — verifies test_offline_lean.t1's goal is
# provable using CryptolToLean.SAWCoreBitvectors_proofs.

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

build_log=$( ( cd "$LAKE_DIR" && lake build ) 2>&1 )
if [ $? -ne 0 ]; then
    echo "lake build failed for $LAKE_DIR; skipping"
    echo "$build_log"
    rm -rf "$PROBE_DIR"
    exit 0
fi

status=0

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
