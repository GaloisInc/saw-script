# Shared harness for intTests/test_lean_soundness_*/ "shape" tests.
#
# These exercise axiom-shape invariants by running Lean's elaborator
# on small hand-written probes. File naming is the entire contract:
#
#   *.shouldfail.lean — MUST FAIL Lean elaboration. A successful
#                       elaboration means the axiom/def was loosened
#                       beyond SAW's declared shape — soundness drift.
#   *.shouldpass.lean — MUST elaborate cleanly AND contain no `sorry`.
#                       These mirror the legitimate translator-emitted
#                       shapes this test guards.
#
# The test fails if any single probe misbehaves. Every probe in the
# test dir matching either suffix is exercised; adding more is just
# dropping files in, no script edits needed.
#
# Each test dir's test.sh is a one-liner that delegates here:
#   exec ${TEST_SHELL:-bash} ../support/lean-shape-test.sh "$@"

set -u

if ! command -v lake >/dev/null 2>&1; then
    echo "lake unavailable; skipping (Lean-only test)"
    exit 0
fi

LAKE_DIR="$(cd ../../saw-core-lean/lean && pwd)"
TEST_NAME="$(basename "$(pwd)")"
PROBE_DIR="$LAKE_DIR/intTestsProbe/$TEST_NAME"

mkdir -p "$PROBE_DIR"
for probe in *.shouldfail.lean *.shouldpass.lean; do
    [ -f "$probe" ] || continue
    cp "$probe" "$PROBE_DIR/$probe"
done

# Make sure the project is up to date. If lake build fails (often:
# HOME overridden so elan can't find its toolchain), treat as skip.
build_log=$( ( cd "$LAKE_DIR" && lake build ) 2>&1 )
if [ $? -ne 0 ]; then
    echo "lake build failed for $LAKE_DIR; skipping (Lean-only test)"
    echo "$build_log"
    rm -rf "$PROBE_DIR"
    exit 0
fi

# Helper: elaborate one probe and check it meets `expect`.
#   expect=fail : expect an "error:" line in output.
#   expect=pass : expect no error and no sorry warning.
status=0
run_probe() {
    local probe="$1"
    local expect="$2"
    local out rc
    out=$( ( cd "$LAKE_DIR" && lake env lean \
              "intTestsProbe/$TEST_NAME/$probe" ) 2>&1 ) && rc=0 || rc=$?
    echo "--- $probe (expected: $expect) ---"
    echo "$out"
    echo "exit=$rc"
    case "$expect" in
      fail)
        if echo "$out" | grep -qE "^[^[:space:]]+: error" ; then
            echo "OK: $probe rejected as designed"
        else
            echo "FAIL: $probe elaborated cleanly — soundness drift!"
            status=1
        fi
        ;;
      pass)
        if [ "$rc" -ne 0 ] || echo "$out" | grep -qE "^[^[:space:]]+: error" ; then
            echo "FAIL: $probe did not elaborate"
            status=1
        elif echo "$out" | grep -q "declaration uses \`sorry\`" ; then
            echo "FAIL: $probe elaborates but uses \`sorry\`"
            status=1
        else
            echo "OK: $probe elaborated as designed"
        fi
        ;;
    esac
}

saw_probe=0
for probe in *.shouldfail.lean; do
    [ -f "$probe" ] || continue
    run_probe "$probe" fail
    saw_probe=1
done
for probe in *.shouldpass.lean; do
    [ -f "$probe" ] || continue
    run_probe "$probe" pass
    saw_probe=1
done

if [ "$saw_probe" -eq 0 ]; then
    echo "FAIL: no *.shouldfail.lean or *.shouldpass.lean probes found"
    status=1
fi

rm -rf "$PROBE_DIR"
exit $status
