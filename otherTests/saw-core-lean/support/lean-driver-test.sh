#!/usr/bin/env bash
# test-lean.sh — drive an integration test for the saw-core-lean
# translation backend. Companion to ../support/test-and-diff.sh, but
# extended to also pin generated .lean output files and (optionally)
# run them through Lean's elaborator.
#
# Usage: bash ../support/test-lean.sh [verb]
# Verbs follow test-and-diff.sh: test (default) | run-tests |
# show-diffs | check-diffs | good | clean.
#
# Conventions for one test directory:
#
#   foo.saw            — the SAW driver. Required.
#   foo.log.good       — expected SAW stdout. Required.
#   foo.<X>.lean       — emitted by foo.saw. Pinned via
#                        foo.<X>.lean.good (one per emitted file).
#   foo.expect-fail    — if present, foo.saw is expected to exit
#                        non-zero. Without it, exit non-zero is a
#                        test failure.
#
# Every emitted *.lean file in this directory after the saw run is fed to
# ../support/lean-elaborate.sh. There is no opt-out flag and no environment
# skip: missing lake, Lake build failure, or Lean elaboration failure is a hard
# test failure.
#
# Exit codes match SAW conventions: 0 = test passed, non-zero = at
# least one diff disagreed or saw misbehaved.

set -u

# offline_lean_replay rows need the checkout root to locate the
# factored checker + pinned library; default it from this script's
# own location when the caller has not set it.
if [ -z "${SAW_LEAN_ROOT:-}" ]; then
    SAW_LEAN_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
fi
export SAW_LEAN_ROOT

# Pick up *.saw test scripts (same logic as test-and-diff.sh).
TESTS=
for SCRIPT in *.saw; do
    if [ "$SCRIPT" = "*.saw" ]; then
        break
    fi
    BASE=${SCRIPT%.saw}
    TESTS="$TESTS $BASE"
done
if [ -z "$TESTS" ]; then
    echo "$0: no *.saw files in $(pwd)" >&2
    exit 1
fi

CURDIR=$(pwd -P || pwd)

# `run-tests` runs SAW for each *.saw and stages outputs.
run-tests() {
    rm -f *.log *.diff *.lean.diff *.lean.elaboration *.lean.elaboration.fail \
          *.lean.obsolete-helpers.fail *.exit.fail
    # Remove generated Lean before running SAW so stale ignored artifacts cannot
    # satisfy .lean.good diffs or elaboration checks.
    for f in *.lean; do
        [ -f "$f" ] || continue
        case "$f" in
            *.lean.good) ;;
            *) rm -f "$f" ;;
        esac
    done

    for TEST in $TESTS; do
        echo "$SAW $TEST.saw"

        # Run SAW. Expected-failure tests must actually fail; otherwise a
        # rejection boundary can silently turn into acceptance while the old log
        # text still happens to match.
        if [ -f "$TEST.expect-fail" ]; then
            $SAW "$TEST.saw" >"$TEST.rawlog" 2>&1
            rc=$?
            if [ "$rc" -eq 0 ]; then
                echo "FAILED: expected $TEST.saw to fail, but SAW exited 0" \
                    >"$TEST.exit.fail"
            fi
        else
            $SAW "$TEST.saw" >"$TEST.rawlog" 2>&1 || \
                echo "FAILED" >>"$TEST.rawlog"
        fi

        # Strip absolute path prefixes from saw's own diagnostic
        # output so the .log.good files are portable across
        # checkout locations.
        sed "s,$CURDIR/,,g; s,\"$CURDIR\",\".\",g" \
            "$TEST.rawlog" >"$TEST.log"

        # Diff stdout.
        diff -u "$TEST.log.good" "$TEST.log" >"$TEST.diff" 2>&1 || true

        # Diff each pinned .lean output. We discover them from the
        # presence of *.lean.good files so adding a new emitted
        # file is just dropping a new .lean.good in.
        for GOOD in *.lean.good; do
            [ -f "$GOOD" ] || continue
            EMITTED="${GOOD%.good}"
            DIFF="${EMITTED%.lean}.lean.diff"
            if [ ! -f "$EMITTED" ]; then
                echo "MISSING: $EMITTED was not emitted by $TEST.saw" \
                    >"$DIFF"
            else
                diff -u "$GOOD" "$EMITTED" >"$DIFF" 2>&1 || true
            fi
        done

        # Lean elaboration of every emitted *.lean file. Mandatory —
        # if any emission doesn't elaborate, the test fails. There is
        # no opt-out flag and no environment-skip: missing lake / build
        # failure / elaboration error all surface as `.lean.elaboration.fail`,
        # which `check-diffs` treats as a hard failure.
        EMITTED_FILES=
        for f in *.lean; do
            [ -f "$f" ] || continue
            case "$f" in
                *.lean.good|*.lean.diff|*.lean.elaboration) ;;
                *) EMITTED_FILES="$EMITTED_FILES $f" ;;
            esac
        done
        if [ -n "$EMITTED_FILES" ]; then
            # The names below are the RETIRED Phase-5 direct fix-lowering
            # helpers (silent-trust surface; residual-trust catalog §3.2).
            # The OP-3 successor's proof-carrying realizations —
            # saw_fix_bounded (Slice R2) and saw_stream_unfold (Slice R3)
            # — are the SANCTIONED replacements under the per-instance
            # PROVEN H_prod obligation (design doc 2026-07-15, amendment
            # A/E): do NOT add them to this list when their emission
            # slices land.
            obsolete_pattern='(^|[^[:alnum:]_])(mkStreamM|mkStreamFix|mkStreamFixM|mkStreamFixPair|mkStreamFixPairM|cryptolIterateM|genFix|genFixM|genFixMChecked|genFixVecChecked|GenFixBodyProductive|GenFixVecBodySound|StreamBodyProductive|PairStreamComponentProductive|PairStreamBodyProductive|saw_unreachable_default|rawifyExceptToRaw|divNatChecked|modNatChecked|BoundedVecFold|h_raw_error_obligation_|saw_fix_unique_contract|saw_fix_unique_exists|saw_fix_choose)([^[:alnum:]_]|$)'
            obsolete_hits=$(grep -nE "$obsolete_pattern" $EMITTED_FILES 2>/dev/null || true)
            if [ -n "$obsolete_hits" ]; then
                {
                    echo "OBSOLETE HELPERS FOUND"
                    echo "$obsolete_hits"
                } >"$TEST.lean.obsolete-helpers.fail"
            fi

            set +e
            bash "$(dirname "$0")/lean-elaborate.sh" $EMITTED_FILES \
                >"$TEST.lean.elaboration" 2>&1
            rc=$?
            set -e
            if [ "$rc" -ne 0 ]; then
                echo "ELABORATION FAILED (rc=$rc)" >"$TEST.lean.elaboration.fail"
            fi
        fi
    done
}

# `show-diffs` cats every non-empty *.diff and *.lean.diff.
show-diffs() {
    for TEST in $TESTS; do
        for d in "$TEST.diff" *.lean.diff; do
            [ -f "$d" ] && [ -s "$d" ] && cat "$d"
        done
        if [ -s "$TEST.lean.elaboration.fail" ] 2>/dev/null; then
            cat "$TEST.lean.elaboration"
        fi
        if [ -s "$TEST.lean.obsolete-helpers.fail" ] 2>/dev/null; then
            cat "$TEST.lean.obsolete-helpers.fail"
        fi
        if [ -s "$TEST.exit.fail" ] 2>/dev/null; then
            cat "$TEST.exit.fail"
        fi
    done
    return 0
}

# `check-diffs` exits 1 if any pinned diff is non-empty or any
# elaboration failed.
check-diffs() {
    failed=0
    for TEST in $TESTS; do
        for d in "$TEST.diff" *.lean.diff; do
            [ -f "$d" ] && [ -s "$d" ] && failed=1
        done
        [ -f "$TEST.lean.elaboration.fail" ] && failed=1
        [ -f "$TEST.lean.obsolete-helpers.fail" ] && failed=1
        [ -f "$TEST.exit.fail" ] && failed=1
    done
    if [ "$failed" -ne 0 ]; then
        cat 1>&2 <<EOF

Unexpected test diffs or Lean-elaboration failures.
If the new outputs are correct, run \`bash test.sh good\` to
update the reference files. Don't do that without thinking.
EOF
        exit 1
    fi
}

# `good` updates *.log.good and every emitted *.lean to its .good.
good() {
    run-tests
    for TEST in $TESTS; do
        if [ -f "$TEST.exit.fail" ]; then
            cat "$TEST.exit.fail" >&2
            exit 1
        fi
        [ -f "$TEST.log" ] && cp "$TEST.log" "$TEST.log.good"
        for f in *.lean; do
            [ -f "$f" ] || continue
            case "$f" in
                *.lean.good|*.lean.diff|*.lean.elaboration) ;;
                *) cp "$f" "$f.good" ;;
            esac
        done
    done
}

clean() {
    rm -f *.rawlog *.log *.diff *.lean.diff *.lean.elaboration \
          *.lean.elaboration.fail *.lean.obsolete-helpers.fail *.exit.fail
    # Remove any emitted .lean files (but never .lean.good).
    for f in *.lean; do
        [ -f "$f" ] || continue
        case "$f" in
            *.lean.good) ;;
            *) rm -f "$f" ;;
        esac
    done
}

test() {
    run-tests
    show-diffs
    check-diffs
}

if [ $# -eq 0 ]; then
    test
else
    for VERB in "$@"; do
        case "$VERB" in
            test)        test ;;
            run-tests)   run-tests ;;
            show-diffs|show)   show-diffs ;;
            check-diffs|check) check-diffs ;;
            good)        good ;;
            clean)       clean ;;
            *) echo "$0: unknown verb $VERB" >&2; exit 1 ;;
        esac
    done
fi

exit 0
