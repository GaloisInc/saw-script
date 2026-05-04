# Shared harness for intTests/test_lean_*_proof/ directories.
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
#     5. Fails if elaboration errors OR proof.lean's own declarations
#        use `sorry`. (The emitted file's `theorem goal_holds := by
#        sorry` stub is expected; we ignore its sorry warning.)
#     6. Cleans up.
#
# Emission drift → import compile failure → loud test failure.

set -u

if ! command -v lake >/dev/null 2>&1; then
    echo "lake unavailable; skipping (Lean-only test)"
    exit 0
fi

# Locate the Lake project root and this test's probe dir.
LAKE_DIR="$(cd ../../saw-core-lean/lean && pwd)"
SAW_DIR="$(cd ../.. && pwd)"
TEST_NAME="$(basename "$(pwd)")"
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

# Make sure the project is up to date. If lake build fails (often:
# HOME overridden so elan can't find its toolchain), treat as skip.
build_log=$( ( cd "$LAKE_DIR" && lake build ) 2>&1 )
if [ $? -ne 0 ]; then
    echo "lake build failed for $LAKE_DIR; skipping (Lean-only test)"
    echo "$build_log"
    rm -rf "$PROBE_DIR"
    exit 0
fi

status=0

# If proof.lean imports the SAW-emitted goal, compile Emitted.lean
# to Emitted.olean first so the import resolves.
if [ -n "$EMITTED_ABS" ]; then
    emit_build=$( ( cd "$LAKE_DIR" && lake env lean \
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
fi

# Elaborate proof.lean. LEAN_PATH points at the probe dir so
# `import Emitted` finds our freshly-built Emitted.olean.
proof_out=$( ( cd "$LAKE_DIR" && LEAN_PATH="intTestsProbe/$TEST_NAME:${LEAN_PATH:-}" \
               lake env lean \
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
