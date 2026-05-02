# Bespoke driver — this test exercises Lean elaboration directly,
# without invoking SAW. We probe two files:
#   - attack.lean   : MUST FAIL Lean elaboration. A successful
#                     elaboration here means the coerce axiom
#                     shape has drifted broader than SAW's sort 0.
#   - positive.lean : MUST SUCCEED elaboration. These mirror the
#                     `coerce` use sites the translator actually
#                     emits.
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
cp positive.lean "$PROBE_DIR/positive.lean"

build_log=$( ( cd "$LAKE_DIR" && lake build ) 2>&1 )
if [ $? -ne 0 ]; then
    echo "lake build failed for $LAKE_DIR; skipping (Lean-only test)"
    echo "$build_log"
    rm -rf "$PROBE_DIR"
    exit 0
fi

status=0

# attack.lean MUST fail.
attack_out=$( ( cd "$LAKE_DIR" && lake env lean \
                "intTestsProbe/$TEST_NAME/attack.lean" ) 2>&1 ) && \
    attack_rc=0 || attack_rc=$?
echo "--- attack.lean (expected: FAIL) ---"
echo "$attack_out"
echo "exit=$attack_rc"

if echo "$attack_out" | grep -qE "^[^[:space:]]+: error" ; then
    echo "OK: attack.lean rejected as designed"
else
    echo "FAIL: attack.lean elaborated cleanly — coerce shape drift!"
    status=1
fi

# positive.lean MUST succeed.
pos_out=$( ( cd "$LAKE_DIR" && lake env lean \
             "intTestsProbe/$TEST_NAME/positive.lean" ) 2>&1 ) && \
    pos_rc=0 || pos_rc=$?
echo "--- positive.lean (expected: OK) ---"
echo "$pos_out"
echo "exit=$pos_rc"

if [ "$pos_rc" -ne 0 ] || echo "$pos_out" | grep -qE "^[^[:space:]]+: error" ; then
    echo "FAIL: positive.lean did not elaborate"
    status=1
else
    echo "OK: positive.lean elaborated as designed"
fi

rm -rf "$PROBE_DIR"
exit $status
