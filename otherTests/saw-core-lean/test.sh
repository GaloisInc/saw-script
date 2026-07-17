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
#   workflows/<name>/      Same harness as drivers/, but the rows are the
#                          RELEASE STORY: end-to-end SAWScript verification
#                          workflows (llvm_verify / prove_print punting
#                          goals through emission-only offline_lean), with
#                          discharges tracked in proofs/ and honest gaps
#                          in proof-gaps/. See README.md for the taxonomy.
#
#   differential/<name>/   TRUE DIFFERENTIAL CONFORMANCE. Run SAW on a small
#                          litmus, run Lean on the SAW-Lean emitted artifact,
#                          and mechanically compare the observed outputs.
#                          This is the only positive executable-test category
#                          that counts as semantic conformance.
#
#   obligations/<name>/    OBLIGATION-SHAPE CONFORMANCE. Run SAW on a small
#                          proof-carrying litmus, compile the emitted Lean
#                          outline, and inspect that artifact for the required
#                          visible contract and forbidden bypasses. These tests
#                          do not prove the obligation; they only pin that the
#                          backend emits the right contract shape.
#
#   proofs/<name>/         Discharge a proof against generator-emitted
#                          Lean. Each subdir has source.txt (path to a
#                          drivers/* emission) + proof.lean (tactic
#                          discharge). The harness imports the emitted
#                          file unchanged and elaborates the proof.
#
#   support-proofs/<name>/ Lean support-library regression proofs that are
#                          intentionally NOT generated proof-backend examples.
#                          These may be self-contained and may import
#                          CryptolToLean directly. They run in the default
#                          sweep, but do not count as proof-discharge examples.
#
#   proof-gaps/<name>/     Preserved proof attempts for obligations that are
#                          intentionally not in the default green proof set.
#                          These are real artifacts, not silent skips: they
#                          document hard proof obligations such as BV-heavy
#                          crypto goals that currently require `bv_decide`
#                          native axioms or exceed current checked automation.
#                          Run manually with the proof harness when working on
#                          that obligation. The default sweep and the `gaps`
#                          verb inventory these directories so they cannot
#                          become invisible skipped tests.
#
#   negative/<name>/        Hand-rolled NEGATIVE Lean probes
#                          (*.shouldfail.lean) that pin support-library
#                          axiom shapes. These exist because negative probes
#                          fundamentally require hand-rolled non-conforming
#                          Lean — there's no generator equivalent.
#                          POSITIVE coverage of "translator-emitted
#                          shapes elaborate" lives in drivers/, not here.
#
#   saw-boundary/<name>/   Run SAW; diff *.log.good. Used for SAW
#                          rejection / boundary-behavior tests where
#                          SAW's diagnostic output is the primary
#                          observable, not its emitted Lean.
#
#                          If a directory contains a `.known-gap` file, a
#                          passing run pins a current backend/library gap,
#                          not final boundary behavior. The final summary
#                          reports these separately so `make conformance`
#                          cannot be mistaken for full parity while gaps
#                          remain.
#
#   stretch/<name>/        Manually-run stress probes that are useful for
#                          future scalability work but are not part of the
#                          default parity/regression sweep.
#
# Verbs:
#   test (default) — run everything; report all failures; nonzero exit
#                    on any failure.
#   run            — alias for test.
#   conformance    — run only true conformance categories:
#                    differential/*, obligations/*, and saw-boundary/*.
#                    Known gaps in these categories are pinned failures,
#                    not evidence of full parity. Do not add
#                    drivers/conformance_* or support-proofs/* here:
#                    proof/library/elaboration checks are not differential
#                    tests unless the harness compares real SAW and Lean
#                    observed outcomes.
#   conformance-strict
#                  — same as conformance, but exits nonzero if any known gaps
#                    remain. Use this for the final parity gate.
#   good           — refresh *.log.good and *.lean.good in every driver
#                    and saw-boundary subdir (no effect on proofs/shape).
#   gaps           — validate and report proof-gaps/* and stretch/* inventory
#                    without trying to make those gaps pass.
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

verb="${1:-test}"

# -----------------------------------------------------------------------------
# SAW availability check. Driver / saw-boundary harnesses invoke
# `$SAW <test>.saw`; without `SAW` set, every per-test harness fails
# with a cryptic "SAW: unbound variable". That's a real failure
# (set -u catches it before any test silently skips), but the user
# learns nothing actionable. Fail upfront with one clear diagnostic
# instead. See task #134 (CI gap: SAW-invoking soundness tests must
# run gated). cabal test path sets SAW=eval saw via Test.hs and puts
# the saw binary on PATH via build-tool-depends; manual local runs
# need `make` (which discovers the dist-newstyle binary) or an
# explicit `SAW=...`. Inventory-only and cleanup verbs do not need SAW.
case "$verb" in
    gaps|proof-gaps|clean) ;;
    *)
        if [ -z "${SAW:-}" ]; then
            cat >&2 <<'EOF'
FAIL: SAW environment variable is not set.

This orchestrator runs the saw-core-lean translator end-to-end:
each test invokes `$SAW some_test.saw` and diffs the output. A
missing SAW means we cannot run any of those tests.

How to fix:
  - Recommended (auto-discovers the locally-built binary):
      make test
  - Or set SAW directly:
      SAW=/path/to/saw bash test.sh test
  - Or run via cabal (puts saw on PATH automatically):
      cabal test saw-core-lean-tests

See otherTests/saw-core-lean/Makefile for the local-dev path.
EOF
            exit 1
        fi
        ;;
esac

# -----------------------------------------------------------------------------
# Failure tracking. We accumulate failures and print them at the end.

declare -a failures=()
declare -a known_gaps=()

record_failure() {
    failures+=("$1")
}

record_known_gap() {
    known_gaps+=("$1")
}

preflight_conformance_inputs() {
    local failed=0
    local d
    local f

    for d in differential/*/; do
        [ -d "$d" ] || continue
        for f in test.saw source.txt lean-observe.lean; do
            if [ ! -f "$d$f" ]; then
                echo "FAIL: $d requires $f for true differential testing" >&2
                failed=1
            fi
        done
        if command -v git >/dev/null 2>&1; then
            if git -C "$HERE" check-ignore -q -- "${d}lean-observe.lean"; then
                echo "FAIL: ${d}lean-observe.lean is ignored by git but is a required test source" >&2
                failed=1
            fi
        fi
    done

    return "$failed"
}

print_summary_and_exit() {
    echo
    echo "================================================================"
    if [ "${#failures[@]}" -eq 0 ]; then
        if [ "${#known_gaps[@]}" -eq 0 ]; then
            echo "ALL TESTS PASSED"
        else
            echo "ALL CHECKED TESTS PASSED, BUT ${#known_gaps[@]} KNOWN GAP(S) ARE PINNED:"
            for g in "${known_gaps[@]}"; do
                echo "  - $g"
            done
            echo
            echo "This is not full backend conformance. Each listed item is a"
            echo "SAWCore feature that is in scope but not yet matched by SAW-Lean."
            if [ "${SAW_LEAN_FAIL_ON_KNOWN_GAPS:-0}" = "1" ]; then
                echo
                echo "Strict conformance requested: failing because known gaps remain."
                exit 1
            fi
        fi
        exit 0
    fi
    echo "${#failures[@]} TEST(S) FAILED:"
    for f in "${failures[@]}"; do
        echo "  - $f"
    done
    if [ "${#known_gaps[@]}" -ne 0 ]; then
        echo
        echo "${#known_gaps[@]} KNOWN GAP(S) ALSO PINNED:"
        for g in "${known_gaps[@]}"; do
            echo "  - $g"
        done
        echo
        echo "Known gaps are tracked failures or stress/proof-gap inventory,"
        echo "not evidence of full backend conformance."
    fi
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
    elif [ "$subverb" = "test" ] && [ -f "$cat/$sub/.known-gap" ]; then
        local reason
        reason="$(tr '\n' ' ' < "$cat/$sub/.known-gap" | sed 's/[[:space:]][[:space:]]*/ /g; s/[[:space:]]*$//')"
        record_known_gap "$cat/$sub${reason:+ — $reason}"
    fi
}

# Iterate categories in a fixed order so the output is deterministic.
iterate_drivers()       { for d in drivers/*/;       do run_one drivers       "$(basename "$d")" lean-driver-test.sh "$@"; done; }
iterate_workflows()     { for d in workflows/*/;     do run_one workflows     "$(basename "$d")" lean-driver-test.sh "$@"; done; }
iterate_differential()  { for d in differential/*/;  do run_one differential  "$(basename "$d")" lean-differential-test.sh "$@"; done; }
iterate_obligations()   { for d in obligations/*/;   do run_one obligations   "$(basename "$d")" lean-obligation-test.sh "$@"; done; }
iterate_saw_boundary()  { for d in saw-boundary/*/;  do run_one saw-boundary  "$(basename "$d")" lean-driver-test.sh "$@"; done; }
iterate_proofs()        { for d in proofs/*/;        do run_one proofs        "$(basename "$d")" lean-proof-test.sh   "$@"; done; }
iterate_support_proofs() { for d in support-proofs/*/; do run_one support-proofs "$(basename "$d")" lean-proof-test.sh "$@"; done; }
iterate_negative()       { for d in negative/*/;       do run_one negative       "$(basename "$d")" lean-shape-test.sh   "$@"; done; }

record_gap_inventory_item() {
    local path="$1"
    local note="$2"
    local title
    if [ -f "$path/GAP.md" ]; then
        title="$(sed -n 's/^# *//p' "$path/GAP.md" | head -1)"
    else
        title="$note"
    fi
    record_known_gap "$path${title:+ — $title}"
}

iterate_gap_inventory() {
    local d

    for d in proof-gaps/*/; do
        [ -d "$d" ] || continue
        if [ ! -f "$d/GAP.md" ]; then
            echo "FAIL: $d is a proof gap but has no GAP.md note" >&2
            record_failure "${d%/} (missing GAP.md)"
        fi
        if [ ! -f "$d/source.txt" ]; then
            echo "FAIL: $d is a proof gap but has no source.txt" >&2
            record_failure "${d%/} (missing source.txt)"
        fi
        record_gap_inventory_item "${d%/}" "proof gap"
    done

    for d in stretch/*/; do
        [ -d "$d" ] || continue
        record_known_gap "${d%/} — stress case excluded from default proof/conformance gates"
    done
}

# -----------------------------------------------------------------------------
# Verb dispatch.

shopt -s nullglob
case "$verb" in
    test|run)
        iterate_drivers
        iterate_workflows
        iterate_differential
        iterate_obligations
        iterate_saw_boundary
        iterate_proofs
        iterate_support_proofs
        iterate_negative
        iterate_gap_inventory
        print_summary_and_exit
        ;;
    conformance)
        preflight_conformance_inputs || record_failure "conformance input preflight"
        iterate_differential
        iterate_obligations
        iterate_saw_boundary
        print_summary_and_exit
        ;;
    conformance-strict)
        SAW_LEAN_FAIL_ON_KNOWN_GAPS=1
        preflight_conformance_inputs || record_failure "conformance input preflight"
        iterate_differential
        iterate_obligations
        iterate_saw_boundary
        print_summary_and_exit
        ;;
    good)
        # Refresh .good files. Only drivers and saw-boundary have them.
        iterate_drivers good
        iterate_workflows good
        iterate_saw_boundary good
        print_summary_and_exit
        ;;
    gaps|proof-gaps)
        iterate_gap_inventory
        print_summary_and_exit
        ;;
    clean)
        iterate_drivers clean
        iterate_workflows clean
        iterate_differential clean
        iterate_obligations clean
        iterate_saw_boundary clean
        iterate_proofs clean
        iterate_support_proofs clean
        iterate_negative clean
        print_summary_and_exit
        ;;
    *)
        echo "$0: unknown verb '$verb' (expected: test, run, conformance, conformance-strict, good, gaps, proof-gaps, clean)" >&2
        exit 1
        ;;
esac
