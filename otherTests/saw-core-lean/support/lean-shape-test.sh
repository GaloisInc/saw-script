# Shared harness for otherTests/saw-core-lean/shape/*/ "shape" tests.
#
# These exercise axiom-shape invariants by running Lean's elaborator
# on small hand-written probes. File naming is the entire contract:
#
#   *.shouldfail.lean — MUST FAIL Lean elaboration. A successful
#                       elaboration means the axiom/def was loosened
#                       beyond SAW's declared shape — soundness drift.
#
# The test fails if any single probe misbehaves. Every probe in the
# test dir matching either suffix is exercised; adding more is just
# dropping files in, no script edits needed.
#
# Each test dir's test.sh is a one-liner that delegates here:
#   exec ${TEST_SHELL:-bash} ../support/lean-shape-test.sh "$@"

set -u

# Verb dispatch. The orchestrator passes one of: test (default), good,
# clean. shape tests have no .good files so `good` is a no-op; `clean`
# removes any leftover probe staging.
VERB="${1:-test}"
RESOLVED_LAKE_DIR="$(cd ../../../../saw-core-lean/lean 2>/dev/null && pwd || true)"
TEST_NAME="$(basename "$(pwd)")"

case "$VERB" in
    good)
        echo "lean-shape-test.sh: 'good' is a no-op for shape tests (no .good files)"
        exit 0
        ;;
    clean)
        if [ -n "$RESOLVED_LAKE_DIR" ]; then
            rm -rf "$RESOLVED_LAKE_DIR/intTestsProbe/$TEST_NAME"
        fi
        exit 0
        ;;
    test)
        ;;
    *)
        echo "lean-shape-test.sh: unknown verb '$VERB'" >&2
        exit 1
        ;;
esac

# Phase A (2026-05-04 audit): no silent skips. lake must be available
# whenever this harness runs. Any environment that lacks lake is
# either misconfigured or doesn't belong running Lean-side soundness
# probes at all.
if ! command -v lake >/dev/null 2>&1; then
    cat >&2 <<'EOF'
FAIL: `lake` is not on PATH.

This harness pins Lean-side soundness invariants by elaborating
*.shouldfail.lean probes. It cannot run without the Lean toolchain.

Install elan + the toolchain pinned in saw-core-lean/lean/lean-toolchain.
EOF
    exit 1
fi

# Test dirs live at otherTests/saw-core-lean/{shape,saw-boundary}/<name>/,
# so saw-core-lean/lean/ is four levels up.
LAKE_DIR="$(cd ../../../../saw-core-lean/lean && pwd)"
TEST_NAME="$(basename "$(pwd)")"

# shellcheck disable=SC1091
. "$(cd ../../support && pwd)/lake-timeout.sh"
PROBE_DIR="$LAKE_DIR/intTestsProbe/$TEST_NAME"

mkdir -p "$PROBE_DIR"
for probe in *.shouldfail.lean; do
    [ -f "$probe" ] || continue
    cp "$probe" "$PROBE_DIR/$probe"
done

# Build the Lake project. A failure here means the support library
# itself didn't compile — that's a real problem, not an environment
# issue, so fail loud.
set +e
build_log=$( ( cd "$LAKE_DIR" && $LAKE_TIMEOUT_CMD lake build ) 2>&1 )
build_rc=$?
set -e
if [ "$build_rc" -ne 0 ]; then
    cat >&2 <<EOF
FAIL: \`lake build\` failed in $LAKE_DIR (rc=$build_rc).

Build log:
$build_log

This indicates the saw-core-lean Lean support library does not
compile. Fix that before re-running soundness probes.
EOF
    rm -rf "$PROBE_DIR"
    exit 1
fi

# Elaborate one *.shouldfail.lean probe. It MUST produce a Lean
# elaboration error — that's the soundness invariant we're pinning.
# (Phase F audit, 2026-05-04: shape tests host *only* negative
# probes. Positive coverage of "translator-emitted shapes elaborate"
# lives in drivers/ where the generator's actual output is checked.)
status=0
run_probe() {
    local probe="$1"
    local out rc
    out=$( ( cd "$LAKE_DIR" && $LAKE_TIMEOUT_CMD lake env lean \
              "intTestsProbe/$TEST_NAME/$probe" ) 2>&1 ) && rc=0 || rc=$?
    echo "--- $probe (expected: fail) ---"
    echo "$out"
    echo "exit=$rc"
    if echo "$out" | grep -qE "^[^[:space:]]+: error" ; then
        echo "OK: $probe rejected as designed"
    else
        echo "FAIL: $probe elaborated cleanly — soundness drift!"
        status=1
    fi
}

saw_probe=0
for probe in *.shouldfail.lean; do
    [ -f "$probe" ] || continue
    run_probe "$probe"
    saw_probe=1
done

if [ "$saw_probe" -eq 0 ]; then
    echo "FAIL: no *.shouldfail.lean probes found in $(pwd)"
    status=1
fi

rm -rf "$PROBE_DIR"
exit $status
