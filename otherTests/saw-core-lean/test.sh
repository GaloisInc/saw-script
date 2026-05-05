#!/usr/bin/env bash
#
# saw-core-lean test orchestrator. ONE entry point for everything.
#
# Categories (each is a subdir of test data — no per-test scripts):
#
#   drivers/<name>/        Run SAW; diff *.log.good and *.lean.good. Then
#                          elaborate every emitted *.lean against the
#                          CryptolToLean Lake project. Catches translator
#                          regressions in shape AND in elaboration.
#
#   proofs/<name>/         Discharge a proof against generator-emitted
#                          Lean. Each subdir has source.txt (path to a
#                          drivers/* emission) + proof.lean (tactic
#                          discharge). The harness imports the emitted
#                          file unchanged and elaborates the proof.
#
#   shape/<name>/          Hand-rolled NEGATIVE Lean probes
#                          (*.shouldfail.lean) that pin support-library
#                          axiom shapes. These exist because attacks
#                          fundamentally require hand-rolled malicious
#                          Lean — there's no generator equivalent.
#                          POSITIVE coverage of "translator-emitted
#                          shapes elaborate" lives in drivers/, not here.
#
#   saw-boundary/<name>/   Run SAW; diff *.log.good. Used for SAW
#                          rejection / boundary-behavior tests where
#                          SAW's diagnostic output is the primary
#                          observable, not its emitted Lean.
#
# Verbs:
#   test (default) — run everything; report all failures; nonzero exit
#                    on any failure.
#   run            — alias for test.
#   good           — refresh *.log.good and *.lean.good in every driver
#                    and saw-boundary subdir (no effect on proofs/shape).
#   clean          — clean transient outputs across all subdirs.
#
# Design rules (do not violate without rewriting this comment block):
#   * NO per-subdir test.sh, Makefile, or README. Subdirs are data only.
#   * NO silent skips. If a tool is missing, every test that needs it
#     fails LOUD; the orchestrator reports it as a failure.
#   * NO dropped errors. Every failure path either fails the orchestrator
#     directly or surfaces via a downstream diff/log check that does.
#   * The orchestrator continues past a failing test so the user sees
#     EVERY failure in one run; final exit code is 1 if any failed.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"

# -----------------------------------------------------------------------------
# Failure tracking. We accumulate failures and print them at the end.

declare -a failures=()

record_failure() {
    failures+=("$1")
}

print_summary_and_exit() {
    echo
    echo "================================================================"
    if [ "${#failures[@]}" -eq 0 ]; then
        echo "ALL TESTS PASSED"
        exit 0
    fi
    echo "${#failures[@]} TEST(S) FAILED:"
    for f in "${failures[@]}"; do
        echo "  - $f"
    done
    echo "================================================================"
    exit 1
}

# -----------------------------------------------------------------------------
# Per-subdir runner. Sets up a clean exit code path; never lets a
# subprocess failure go unrecorded.

run_one() {
    local cat="$1"
    local sub="$2"
    local harness="$3"
    local subverb="${4:-test}"
    echo
    echo "=== $cat/$sub ($subverb) ==="
    local rc=0
    ( cd "$cat/$sub" && bash "$HERE/support/$harness" "$subverb" ) || rc=$?
    if [ "$rc" -ne 0 ]; then
        record_failure "$cat/$sub (exit=$rc, harness=$harness)"
    fi
}

# Iterate categories in a fixed order so the output is deterministic.
iterate_drivers()       { for d in drivers/*/;       do run_one drivers       "$(basename "$d")" lean-driver-test.sh "$@"; done; }
iterate_saw_boundary()  { for d in saw-boundary/*/;  do run_one saw-boundary  "$(basename "$d")" lean-driver-test.sh "$@"; done; }
iterate_proofs()        { for d in proofs/*/;        do run_one proofs        "$(basename "$d")" lean-proof-test.sh   "$@"; done; }
iterate_shape()         { for d in shape/*/;         do run_one shape         "$(basename "$d")" lean-shape-test.sh   "$@"; done; }

# -----------------------------------------------------------------------------
# Verb dispatch.

shopt -s nullglob

verb="${1:-test}"
case "$verb" in
    test|run)
        iterate_drivers
        iterate_saw_boundary
        iterate_proofs
        iterate_shape
        print_summary_and_exit
        ;;
    good)
        # Refresh .good files. Only drivers and saw-boundary have them.
        iterate_drivers good
        iterate_saw_boundary good
        print_summary_and_exit
        ;;
    clean)
        iterate_drivers clean
        iterate_saw_boundary clean
        iterate_proofs clean
        iterate_shape clean
        print_summary_and_exit
        ;;
    *)
        echo "$0: unknown verb '$verb' (expected: test, run, good, clean)" >&2
        exit 1
        ;;
esac
