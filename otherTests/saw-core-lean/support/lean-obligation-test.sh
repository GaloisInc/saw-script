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
#   contains:<literal>             emitted Lean must contain <literal>
#   contains-normalized:<literal>  emitted Lean with collapsed whitespace must
#                                  contain <literal> with collapsed whitespace
#   absent:<literal>               emitted Lean must not contain <literal>
#
# Optional:
#
#   forbidden.txt       one forbidden literal per non-comment line.
#   lean-observe.lean   Lean observer importing the emitted artifact as
#                       `Emitted`. Used for generated-artifact behavior that
#                       is not a source-level differential observation, such as
#                       checking that an emitted wrapper propagates an
#                       `Except.error` argument instead of defaulting it.
#   lean-expected.txt   expected normalized `LEAN_OBSERVED: ...` payloads for
#                       lean-observe.lean, one per line. Required when
#                       lean-observe.lean is present.
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
        rm -f *.rawlog *.log *.lean.log *.observed *.observed.diff \
              lean.observed lean.observed.diff known-gap.actual
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
if [ -f lean-observe.lean ] && [ ! -f lean-expected.txt ]; then
    echo "FAIL: obligation observer requires lean-expected.txt" >&2
    exit 1
fi
if [ -f lean-expected.txt ] && [ ! -f lean-observe.lean ]; then
    echo "FAIL: lean-expected.txt requires lean-observe.lean" >&2
    exit 1
fi
if [ -f lean-observe.lean ] && \
   ! grep -Eq '^[[:space:]]*import[[:space:]]+Emitted([[:space:]]|$)' lean-observe.lean; then
    echo "FAIL: lean-observe.lean must import the emitted artifact as Emitted" >&2
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
if [ -f lean-observe.lean ]; then
    cp lean-observe.lean "$PROBE_DIR/lean-observe.lean"
fi

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

if [ -f lean-observe.lean ]; then
    lean_out=$( ( cd "$LAKE_DIR" && LEAN_PATH="intTestsProbe/$PROBE_NAME:${LEAN_PATH:-}" \
                  $LAKE_TIMEOUT_CMD lake env lean \
                  "intTestsProbe/$PROBE_NAME/lean-observe.lean" ) 2>&1 ) && \
        lean_rc=0 || lean_rc=$?
    printf '%s\n' "$lean_out" >test.lean.log
    if [ "$lean_rc" -ne 0 ] || printf '%s\n' "$lean_out" | grep -qE '^[^"[:space:]][^:]*: error' ; then
        cat test.lean.log
        echo "FAIL: Lean obligation observer failed" >&2
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
        echo "FAIL: Lean obligation observer did not contain any LEAN_OBSERVED lines" >&2
        rm -rf "$PROBE_DIR"
        exit 1
    }

    if ! diff -u lean-expected.txt lean.observed >lean.observed.diff 2>&1; then
        echo "--- expected Lean obligation observer ---"
        cat lean-expected.txt
        echo "--- actual Lean obligation observer ---"
        cat lean.observed
        echo "--- diff ---"
        cat lean.observed.diff
        echo "FAIL: Lean obligation observer output changed" >&2
        rm -rf "$PROBE_DIR"
        exit 1
    fi
fi

status=0
: >test.observed

normalize_ws() {
    tr '\n' ' ' | sed 's/[[:space:]][[:space:]]*/ /g; s/^ //; s/ $//'
}

check_contains() {
    local literal="$1"
    if grep -F "$literal" "$emitted" >/dev/null 2>&1; then
        echo "OBLIGATION_OBSERVED: contains:$literal" >>test.observed
    else
        echo "MISSING EXPECTED OBLIGATION: contains:$literal" >&2
        status=1
    fi
}

check_contains_normalized() {
    local literal="$1"
    local normalized_emitted
    local normalized_literal
    normalized_emitted="$(normalize_ws < "$emitted")"
    normalized_literal="$(printf '%s' "$literal" | normalize_ws)"
    if printf '%s\n' "$normalized_emitted" | grep -F "$normalized_literal" >/dev/null 2>&1; then
        echo "OBLIGATION_OBSERVED: contains-normalized:$literal" >>test.observed
    else
        echo "MISSING EXPECTED NORMALIZED OBLIGATION: contains-normalized:$literal" >&2
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
        contains-normalized:*) check_contains_normalized "${directive#contains-normalized:}" ;;
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
  /^contains-normalized:/ { print "OBLIGATION_OBSERVED: " $0; next }
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
