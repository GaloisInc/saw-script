# Shared harness for otherTests/saw-core-lean/proofs/*/ directories.
#
# Discharge pattern:
#
#   Each test dir contains:
#     source.txt  — one line: relative path (from saw-script/) to the
#                   SAW-emitted .lean file whose `goal` we discharge.
#                   The emitted file is never modified.
#     proof.lean  — the discharge. Does `import Emitted` to get `goal`
#                   in scope, then proves a theorem closing it.
#     test.sh     — one-liner: exec ../support/lean-proof-test.sh "$@"
#
#   The harness:
#     1. Reads source.txt for the emitted-file path.
#     2. Copies the emitted file to saw-core-lean/lean/Emitted.lean
#        (project root, so `import Emitted` resolves).
#     3. Copies proof.lean into the per-test probe dir.
#     4. Runs `lake env lean` on proof.lean.
#     5. Fails if elaboration errors, if proof.lean's own declarations
#        use `sorry`, or if the emitted file contains any `sorry`
#        other than the standard `theorem goal_holds := by sorry`
#        emit-stage stub.
#     6. Cleans up.
#
# Emission drift → import compile failure → loud test failure.

set -u

# Verb dispatch. The orchestrator passes one of: test (default), good,
# clean. proof tests have no .good files so `good` is a no-op; `clean`
# removes any leftover probe staging.
VERB="${1:-test}"

# Resolve probe dir early so `clean` can use it without further setup.
RESOLVED_LAKE_DIR="$(cd ../../../../saw-core-lean/lean 2>/dev/null && pwd || true)"
TEST_NAME="$(basename "$(pwd)")"

case "$VERB" in
    good)
        # No-op for proof tests. Loud so it's not mistaken for a skip.
        echo "lean-proof-test.sh: 'good' is a no-op for proof tests (no .good files)"
        exit 0
        ;;
    clean)
        if [ -n "$RESOLVED_LAKE_DIR" ]; then
            rm -rf "$RESOLVED_LAKE_DIR/intTestsProbe/$TEST_NAME"
        fi
        exit 0
        ;;
    test)
        ;;  # fall through to the main test logic below
    *)
        echo "lean-proof-test.sh: unknown verb '$VERB'" >&2
        exit 1
        ;;
esac

# Phase A (2026-05-04 audit): no silent skips. lake must be available
# whenever this harness runs.
if ! command -v lake >/dev/null 2>&1; then
    cat >&2 <<'EOF'
FAIL: `lake` is not on PATH.

This harness discharges Lean-side proof obligations against
SAW-emitted goals. It cannot run without the Lean toolchain.

Install elan + the toolchain pinned in saw-core-lean/lean/lean-toolchain.
EOF
    exit 1
fi

# Locate the Lake project root and this test's probe dir.
# Test dirs live at otherTests/saw-core-lean/proofs/<name>/, so the
# Lake project (saw-core-lean/lean/) is four levels up, and the
# saw-script root is also four levels up.
LAKE_DIR="$(cd ../../../../saw-core-lean/lean && pwd)"
SAW_DIR="$(cd ../../../.. && pwd)"
TEST_NAME="$(basename "$(pwd)")"

# shellcheck disable=SC1091
. "$(cd ../../support && pwd)/lake-timeout.sh"
PROBE_DIR="$LAKE_DIR/intTestsProbe/$TEST_NAME"

# source.txt (optional) names the SAW-emitted .lean file this
# test discharges, relative to the saw-script root. If present,
# it is copied into the probe dir as Emitted.lean so proof.lean
# can `import Emitted`. If absent, proof.lean is expected to be
# self-contained (no emitted goal).
EMITTED_ABS=""
if [ -f source.txt ]; then
    EMITTED_REL=$(head -n1 source.txt)
    EMITTED_ABS="$SAW_DIR/$EMITTED_REL"
    if [ ! -f "$EMITTED_ABS" ]; then
        echo "FAIL: emitted file $EMITTED_ABS (from source.txt) not found"
        exit 1
    fi
fi

mkdir -p "$PROBE_DIR"
if [ -n "$EMITTED_ABS" ]; then
    cp "$EMITTED_ABS" "$PROBE_DIR/Emitted.lean"
fi
cp proof.lean "$PROBE_DIR/proof.lean"

# Build the Lake project. A failure here means the support library
# itself didn't compile — that's a real problem, not an environment
# issue, so fail loud (Phase A audit, 2026-05-04).
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
compile. Fix that before re-running proof discharges.
EOF
    rm -rf "$PROBE_DIR"
    exit 1
fi

status=0

# If proof.lean imports the SAW-emitted goal, compile Emitted.lean
# to Emitted.olean first so the import resolves.
if [ -n "$EMITTED_ABS" ]; then
    emit_build=$( ( cd "$LAKE_DIR" && $LAKE_TIMEOUT_CMD lake env lean \
                      -o "intTestsProbe/$TEST_NAME/Emitted.olean" \
                      "intTestsProbe/$TEST_NAME/Emitted.lean" ) 2>&1 ) && \
        emit_rc=0 || emit_rc=$?
    if [ "$emit_rc" -ne 0 ]; then
        echo "--- Emitted.lean (must compile) ---"
        echo "$emit_build"
        echo "FAIL: emitted .lean did not compile — emission drift"
        rm -rf "$PROBE_DIR"
        exit 1
    fi
    bad_emitted_sorry=$(awk '
      /theorem[[:space:]]+goal_holds[[:space:]]*:/ {
        allow_goal_holds_sorry = 1
        next
      }
      /^[[:space:]]*sorry[[:space:]]*$/ && allow_goal_holds_sorry {
        allow_goal_holds_sorry = 0
        next
      }
      /sorry/ {
        print FILENAME ":" FNR ":" $0
        bad = 1
      }
      {
        allow_goal_holds_sorry = 0
      }
      END { exit bad }
    ' "$PROBE_DIR/Emitted.lean" 2>/dev/null || true)
    if [ -n "$bad_emitted_sorry" ]; then
        echo "--- Emitted.lean (completed proof must not depend on sorry) ---"
        echo "$bad_emitted_sorry"
        echo "FAIL: emitted .lean contains unresolved proof obligations"
        rm -rf "$PROBE_DIR"
        exit 1
    fi
fi

# Elaborate proof.lean. LEAN_PATH points at the probe dir so
# `import Emitted` finds our freshly-built Emitted.olean.
proof_out=$( ( cd "$LAKE_DIR" && LEAN_PATH="intTestsProbe/$TEST_NAME:${LEAN_PATH:-}" \
               $LAKE_TIMEOUT_CMD lake env lean \
                "intTestsProbe/$TEST_NAME/proof.lean" ) 2>&1 ) && \
    proof_rc=0 || proof_rc=$?
echo "--- proof.lean (expected: OK) ---"
echo "$proof_out"
echo "exit=$proof_rc"

if [ "$proof_rc" -ne 0 ] || echo "$proof_out" | grep -qE "^[^[:space:]]+: error" ; then
    echo "FAIL: proof.lean did not elaborate cleanly"
    status=1
elif echo "$proof_out" | \
     grep -qE "intTestsProbe/$TEST_NAME/proof\.lean:.*declaration uses .sorry." ; then
    echo "FAIL: proof.lean elaborates but its own declarations use \`sorry\`"
    status=1
else
    echo "OK: proof.lean elaborated; tactic discharged goal"
fi

rm -rf "$PROBE_DIR"
exit $status
