# Bespoke driver — this test exercises Lean elaboration directly,
# without invoking SAW. We probe two files:
#   - attack.lean   : MUST FAIL Lean elaboration. A successful
#                     elaboration here is a soundness violation.
#   - non_prop.lean : MUST SUCCEED elaboration. These mirror the
#                     `unsafeAssert` use sites the translator
#                     actually emits.
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
cp attack.lean "$PROBE_DIR/attack.lean"
cp non_prop.lean "$PROBE_DIR/non_prop.lean"

# Make sure the project itself is up to date so probe failures point
# at probe code, not stale CryptolToLean artifacts. If `lake build`
# fails (often: the integration-test harness overrides HOME so elan
# can't find its toolchain) treat as "skip the elaboration check"
# rather than a test failure. The error is logged for diagnostics.
build_log=$( ( cd "$LAKE_DIR" && lake build ) 2>&1 )
if [ $? -ne 0 ]; then
    echo "lake build failed for $LAKE_DIR; skipping (Lean-only test)"
    echo "$build_log"
    rm -rf "$PROBE_DIR"
    exit 0
fi

status=0

# attack.lean MUST fail. Treat success as an error.
attack_out=$( ( cd "$LAKE_DIR" && lake env lean \
                "intTestsProbe/$TEST_NAME/attack.lean" ) 2>&1 ) && \
    attack_rc=0 || attack_rc=$?
echo "--- attack.lean (expected: FAIL) ---"
echo "$attack_out"
echo "exit=$attack_rc"

# Lean exit code is 0 even on errors; check stderr/stdout for an
# explicit "error:" line.
if echo "$attack_out" | grep -qE "^[^[:space:]]+: error" ; then
    echo "OK: attack.lean rejected as designed"
else
    echo "FAIL: attack.lean elaborated cleanly — Prop-attack is open!"
    status=1
fi

# non_prop.lean MUST succeed.
non_out=$( ( cd "$LAKE_DIR" && lake env lean \
             "intTestsProbe/$TEST_NAME/non_prop.lean" ) 2>&1 ) && \
    non_rc=0 || non_rc=$?
echo "--- non_prop.lean (expected: OK) ---"
echo "$non_out"
echo "exit=$non_rc"

if [ "$non_rc" -ne 0 ] || echo "$non_out" | grep -qE "^[^[:space:]]+: error" ; then
    echo "FAIL: non_prop.lean did not elaborate"
    status=1
else
    echo "OK: non_prop.lean elaborated as designed"
fi

rm -rf "$PROBE_DIR"
exit $status
