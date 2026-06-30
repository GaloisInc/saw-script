#!/usr/bin/env bash
#
# Obligation-shape harness for otherTests/saw-core-lean/obligations/*.
#
# Contract for each directory:
#
#   test.saw      runs the real SAW producer and emits a Lean artifact.
#   source.txt    one line: emitted Lean filename, relative to this dir.
#   expected.txt  normalized facts the emitted artifact must expose.
#
# expected.txt directives:
#
#   contains:<literal>  emitted Lean must contain <literal>
#   absent:<literal>    emitted Lean must not contain <literal>
#
# Optional:
#
#   forbidden.txt       one forbidden literal per non-comment line.
#   .known-gap          reason reported in the conformance summary.
#   .known-gap.expected diagnostic substrings required when the positive
#                       obligation check fails.
#
# This is a shape test over generated artifacts, not proof discharge. Emitted
# outlines may contain local `by sorry` placeholders; completed proof tests are
# responsible for rejecting unresolved placeholders.

set -u

VERB="${1:-test}"
RESOLVED_LAKE_DIR="$(cd ../../../../saw-core-lean/lean 2>/dev/null && pwd || true)"
TEST_NAME="$(basename "$(pwd)")"

case "$VERB" in
    clean)
        rm -f *.rawlog *.log *.observed *.observed.diff known-gap.actual
        if [ -f source.txt ]; then
            emitted=$(head -n1 source.txt)
            [ -n "$emitted" ] && rm -f "$emitted"
        fi
        if [ -n "$RESOLVED_LAKE_DIR" ]; then
            rm -rf "$RESOLVED_LAKE_DIR/intTestsProbe/obligation_$TEST_NAME"
        fi
        exit 0
        ;;
    good)
        echo "lean-obligation-test.sh: 'good' is intentionally unsupported"
        echo "Obligation tests compare generated shape facts, not goldens."
        exit 1
        ;;
    test)
        ;;
    *)
        echo "lean-obligation-test.sh: unknown verb '$VERB'" >&2
        exit 1
        ;;
esac

if [ -z "${SAW:-}" ]; then
    echo "FAIL: SAW environment variable is not set." >&2
    exit 1
fi

if ! command -v lake >/dev/null 2>&1; then
    echo "FAIL: lake is not on PATH (cannot compile emitted Lean outline)." >&2
    exit 1
fi

if [ ! -f test.saw ]; then
    echo "FAIL: obligation test requires test.saw" >&2
    exit 1
fi

if [ ! -f source.txt ]; then
    echo "FAIL: obligation test requires source.txt naming emitted Lean" >&2
    exit 1
fi

if [ ! -f expected.txt ]; then
    echo "FAIL: obligation test requires expected.txt" >&2
    exit 1
fi

if [ -f .known-gap ] && [ -z "${SAW_LEAN_OBLIGATION_KNOWN_GAP_INNER:-}" ]; then
    if [ ! -f .known-gap.expected ]; then
        echo "FAIL: obligation known gap requires .known-gap.expected" >&2
        exit 1
    fi

    set +e
    SAW_LEAN_OBLIGATION_KNOWN_GAP_INNER=1 bash "$0" test \
        >known-gap.actual 2>&1
    gap_rc=$?
    set -u

    if [ "$gap_rc" -eq 0 ]; then
        cat known-gap.actual
        echo "FAIL: known-gap obligation test unexpectedly passed" >&2
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
        echo "FAIL: known-gap obligation diagnostic changed" >&2
        exit 1
    fi

    echo "OK: known obligation gap pinned"
    exit 0
fi

LAKE_DIR="$(cd ../../../../saw-core-lean/lean && pwd)"
PROBE_NAME="obligation_$TEST_NAME"
PROBE_DIR="$LAKE_DIR/intTestsProbe/$PROBE_NAME"

# shellcheck disable=SC1091
. "$(cd ../../support && pwd)/lake-timeout.sh"

rm -f *.rawlog *.log *.observed *.observed.diff
rm -rf "$PROBE_DIR"

emitted=$(head -n1 source.txt)
if [ -z "$emitted" ]; then
    echo "FAIL: source.txt is empty" >&2
    exit 1
fi

echo "$SAW test.saw"
if ! "$SAW" test.saw >test.rawlog 2>&1; then
    cat test.rawlog
    echo "FAIL: SAW obligation producer failed" >&2
    exit 1
fi
sed "s,$(pwd -P || pwd)/,,g; s,\"$(pwd -P || pwd)\",\".\",g" \
    test.rawlog >test.log

if [ ! -f "$emitted" ]; then
    cat test.log
    echo "FAIL: expected emitted Lean file '$emitted' was not produced" >&2
    exit 1
fi

mkdir -p "$PROBE_DIR"
cp "$emitted" "$PROBE_DIR/Emitted.lean"

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
    echo "FAIL: emitted Lean obligation outline did not compile" >&2
    rm -rf "$PROBE_DIR"
    exit 1
fi

status=0
: >test.observed

check_contains() {
    local literal="$1"
    if grep -F "$literal" "$emitted" >/dev/null 2>&1; then
        echo "OBLIGATION_OBSERVED: contains:$literal" >>test.observed
    else
        echo "MISSING EXPECTED OBLIGATION: contains:$literal" >&2
        status=1
    fi
}

check_absent() {
    local literal="$1"
    local record="${2:-yes}"
    if grep -F "$literal" "$emitted" >/dev/null 2>&1; then
        echo "FORBIDDEN OBLIGATION BYPASS PRESENT: absent:$literal" >&2
        status=1
    elif [ "$record" = "yes" ]; then
        echo "OBLIGATION_OBSERVED: absent:$literal" >>test.observed
    fi
}

while IFS= read -r directive || [ -n "$directive" ]; do
    case "$directive" in
        ''|\#*) continue ;;
        contains:*) check_contains "${directive#contains:}" ;;
        absent:*) check_absent "${directive#absent:}" ;;
        *)
            echo "FAIL: unknown expected.txt directive: $directive" >&2
            status=1
            ;;
    esac
done < expected.txt

if [ -f forbidden.txt ]; then
    while IFS= read -r literal || [ -n "$literal" ]; do
        case "$literal" in
            ''|\#*) continue ;;
        esac
        check_absent "$literal" no
    done < forbidden.txt
fi

awk '
  /^contains:/ { print "OBLIGATION_OBSERVED: " $0; next }
  /^absent:/ { print "OBLIGATION_OBSERVED: " $0; next }
  /^#/ || /^$/ { next }
  { print "INVALID_EXPECTED_DIRECTIVE: " $0 }
' expected.txt >expected.observed

if ! diff -u expected.observed test.observed >test.observed.diff 2>&1; then
    cat test.observed.diff
    echo "FAIL: obligation observation changed" >&2
    status=1
fi

if [ "$status" -eq 0 ]; then
    echo "OK: obligation shape matches"
fi

rm -rf "$PROBE_DIR"
exit "$status"
