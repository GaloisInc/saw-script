#!/usr/bin/env bash
#
# TRUE differential harness for otherTests/saw-core-lean/differential/*.
#
# Contract for each directory:
#   test.saw          runs the real SAW-side case, prints one or more
#                     `SAW_OBSERVED: ...` lines, and emits a Lean file.
#   source.txt        one line: the emitted Lean filename, relative to this dir.
#   lean-observe.lean imports `Emitted` and prints matching
#                     `LEAN_OBSERVED: ...` lines by evaluating/checking the
#                     emitted definition itself.
#
# A passing test means:
#   1. SAW ran the litmus and produced observed outcome lines.
#   2. Lean compiled the SAW-Lean emitted artifact.
#   3. Lean ran the observer against that emitted artifact.
#   4. The normalized SAW and Lean observed outcome lines are identical.
#
# If a directory contains `.known-gap`, this harness instead expects the real
# differential run to fail and requires `.known-gap.expected` to list stable
# diagnostic substrings that must appear in `known-gap.actual`. This is for
# pinning current backend gaps only; it is not parity evidence.
#
# This harness deliberately does NOT accept golden diffs, standalone Lean
# support-library proofs, or "Lean elaborated" as differential evidence.

set -u

VERB="${1:-test}"

RESOLVED_LAKE_DIR="$(cd ../../../../saw-core-lean/lean 2>/dev/null && pwd || true)"
TEST_NAME="$(basename "$(pwd)")"

case "$VERB" in
    clean)
        rm -f *.rawlog *.log *.lean.log *.observed *.observed.diff \
              known-gap.actual
        if [ -n "$RESOLVED_LAKE_DIR" ]; then
            rm -rf "$RESOLVED_LAKE_DIR/intTestsProbe/differential_$TEST_NAME"
        fi
        if [ -f source.txt ]; then
            emitted=$(head -n1 source.txt)
            [ -n "$emitted" ] && rm -f "$emitted"
        fi
        exit 0
        ;;
    good)
        echo "lean-differential-test.sh: 'good' is intentionally unsupported"
        echo "Differential tests compare live SAW and Lean observations, not goldens."
        exit 1
        ;;
    test)
        ;;
    *)
        echo "lean-differential-test.sh: unknown verb '$VERB'" >&2
        exit 1
        ;;
esac

if [ -z "${SAW:-}" ]; then
    echo "FAIL: SAW environment variable is not set." >&2
    exit 1
fi

if ! command -v lake >/dev/null 2>&1; then
    echo "FAIL: lake is not on PATH (cannot run Lean observation)." >&2
    exit 1
fi

if [ ! -f test.saw ]; then
    echo "FAIL: differential test requires test.saw" >&2
    exit 1
fi

if [ ! -f source.txt ]; then
    echo "FAIL: differential test requires source.txt naming emitted Lean" >&2
    exit 1
fi

if [ ! -f lean-observe.lean ]; then
    echo "FAIL: differential test requires lean-observe.lean" >&2
    exit 1
fi

if ! grep -Eq '^[[:space:]]*import[[:space:]]+Emitted([[:space:]]|$)' lean-observe.lean; then
    echo "FAIL: lean-observe.lean must import the emitted artifact as Emitted" >&2
    exit 1
fi

if ! grep -Eq '(^|[^[:alnum:]_])(Observed|Emitted\.)([^[:alnum:]_]|$)' lean-observe.lean; then
    echo "FAIL: lean-observe.lean must reference the emitted observation, not a rebuilt value" >&2
    exit 1
fi

if [ -f .known-gap ] && [ -z "${SAW_LEAN_DIFFERENTIAL_KNOWN_GAP_INNER:-}" ]; then
    if [ ! -f .known-gap.expected ]; then
        echo "FAIL: differential known gap requires .known-gap.expected" >&2
        exit 1
    fi

    set +e
    SAW_LEAN_DIFFERENTIAL_KNOWN_GAP_INNER=1 bash "$0" test \
        >known-gap.actual 2>&1
    gap_rc=$?
    set -u

    if [ "$gap_rc" -eq 0 ]; then
        cat known-gap.actual
        echo "FAIL: known-gap differential test unexpectedly passed" >&2
        exit 1
    fi

    missing=0
    while IFS= read -r expected || [ -n "$expected" ]; do
        case "$expected" in
            ''|\#*) continue ;;
        esac
        if ! grep -F "$expected" known-gap.actual >/dev/null 2>&1; then
            echo "MISSING EXPECTED KNOWN-GAP DIAGNOSTIC: $expected" >&2
            missing=1
        fi
    done < .known-gap.expected

    if [ "$missing" -ne 0 ]; then
        cat known-gap.actual
        echo "FAIL: known-gap differential diagnostic changed" >&2
        exit 1
    fi

    echo "OK: known differential gap pinned"
    exit 0
fi

LAKE_DIR="$(cd ../../../../saw-core-lean/lean && pwd)"
PROBE_NAME="differential_$TEST_NAME"
PROBE_DIR="$LAKE_DIR/intTestsProbe/$PROBE_NAME"

# shellcheck disable=SC1091
. "$(cd ../../support && pwd)/lake-timeout.sh"

rm -f *.rawlog *.log *.lean.log *.observed *.observed.diff
rm -rf "$PROBE_DIR"

emitted=$(head -n1 source.txt)
if [ -z "$emitted" ]; then
    echo "FAIL: source.txt is empty" >&2
    exit 1
fi
case "$emitted" in
    /*|../*|*/../*|*.lean.good)
        echo "FAIL: source.txt must name a local generated .lean output, got '$emitted'" >&2
        exit 1
        ;;
    *.lean)
        ;;
    *)
        echo "FAIL: source.txt must name a generated .lean output, got '$emitted'" >&2
        exit 1
        ;;
esac

# Remove the expected output before running SAW. A successful producer must
# create the artifact in this run; ignored stale .lean files are not evidence.
rm -f -- "$emitted"

echo "$SAW test.saw"
if ! "$SAW" test.saw >test.rawlog 2>&1; then
    cat test.rawlog
    echo "FAIL: SAW differential producer failed" >&2
    exit 1
fi
sed "s,$(pwd -P || pwd)/,,g; s,\"$(pwd -P || pwd)\",\".\",g" \
    test.rawlog >test.log

awk '
  /^SAW_OBSERVED:[[:space:]]*/ {
    sub(/^SAW_OBSERVED:[[:space:]]*/, "")
    print
    found = 1
  }
  END { if (!found) exit 1 }
' test.log >saw.observed || {
    cat test.log
    echo "FAIL: SAW log did not contain any SAW_OBSERVED lines" >&2
    exit 1
}

if [ ! -f "$emitted" ]; then
    cat test.log
    echo "FAIL: expected emitted Lean file '$emitted' was not produced" >&2
    exit 1
fi

mkdir -p "$PROBE_DIR"
cp "$emitted" "$PROBE_DIR/Emitted.lean"
cp lean-observe.lean "$PROBE_DIR/lean-observe.lean"

set +e
build_log=$( ( cd "$LAKE_DIR" && $LAKE_TIMEOUT_CMD lake build ) 2>&1 )
build_rc=$?
set -e
if [ "$build_rc" -ne 0 ]; then
    echo "FAIL: lake build failed in $LAKE_DIR (rc=$build_rc)" >&2
    echo "$build_log" >&2
    rm -rf "$PROBE_DIR"
    exit 1
fi

emit_out=$( ( cd "$LAKE_DIR" && $LAKE_TIMEOUT_CMD lake env lean \
                 -o "intTestsProbe/$PROBE_NAME/Emitted.olean" \
                 "intTestsProbe/$PROBE_NAME/Emitted.lean" ) 2>&1 ) && \
    emit_rc=0 || emit_rc=$?
if [ "$emit_rc" -ne 0 ]; then
    echo "$emit_out"
    echo "FAIL: emitted Lean artifact did not compile" >&2
    rm -rf "$PROBE_DIR"
    exit 1
fi
if printf '%s\n' "$emit_out" | grep -F 'uses `sorry`' >/dev/null 2>&1; then
    echo "$emit_out"
    echo "FAIL: true differential executable tests may not rely on proof stubs" >&2
    rm -rf "$PROBE_DIR"
    exit 1
fi

lean_out=$( ( cd "$LAKE_DIR" && LEAN_PATH="intTestsProbe/$PROBE_NAME:${LEAN_PATH:-}" \
              $LAKE_TIMEOUT_CMD lake env lean \
              "intTestsProbe/$PROBE_NAME/lean-observe.lean" ) 2>&1 ) && \
    lean_rc=0 || lean_rc=$?
printf '%s\n' "$lean_out" >test.lean.log
if [ "$lean_rc" -ne 0 ] || printf '%s\n' "$lean_out" | grep -qE "^[^[:space:]]+: error" ; then
    cat test.lean.log
    echo "FAIL: Lean observer failed" >&2
    rm -rf "$PROBE_DIR"
    exit 1
fi

awk '
  /^"?LEAN_OBSERVED:[[:space:]]*/ {
    sub(/^"?LEAN_OBSERVED:[[:space:]]*/, "")
    sub(/"$/, "")
    print
    found = 1
  }
  END { if (!found) exit 1 }
' test.lean.log >lean.observed || {
    cat test.lean.log
    echo "FAIL: Lean log did not contain any LEAN_OBSERVED lines" >&2
    rm -rf "$PROBE_DIR"
    exit 1
}

if ! diff -u saw.observed lean.observed >test.observed.diff 2>&1; then
    echo "--- SAW observed ---"
    cat saw.observed
    echo "--- Lean observed ---"
    cat lean.observed
    echo "--- diff ---"
    cat test.observed.diff
    echo "FAIL: SAW and Lean observations differ" >&2
    rm -rf "$PROBE_DIR"
    exit 1
fi

echo "OK: SAW and Lean observations match"
rm -rf "$PROBE_DIR"
exit 0
