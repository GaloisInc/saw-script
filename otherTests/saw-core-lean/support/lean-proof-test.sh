#!/usr/bin/env bash
# Shared harness for otherTests/saw-core-lean/proofs/*/ and
# support-lemmas/*/ directories.
#
# Discharge pattern:
#
#   Each test dir contains:
#     source.txt  — one line: relative path (from saw-script/) to the
#                   SAW-emitted .lean file whose `goal` we discharge.
#                   The emitted file is never modified.
#     proof.lean  — the discharge. Does `import Emitted` to get `goal`
#                   in scope, then proves a theorem closing it.
#     completed.lean (optional)
#                 — a completed copy of the generated outline. Use this
#                   for generated files that contain side-condition proof
#                   placeholders inside definitions: the user edits the
#                   outline itself, removes every `sorry`, and the harness
#                   replays that checked artifact as `Emitted`.
#     test.sh     — one-liner: exec ../support/lean-proof-test.sh "$@"
#
#   The harness:
#     1. Reads source.txt for the emitted-file path.
#     2. Copies completed.lean, if present, otherwise the emitted file,
#        to saw-core-lean/lean/Emitted.lean (project root, so
#        `import Emitted` resolves). For completed.lean, also imports
#        the tracked emitted artifact under a private namespace and
#        checks that the completed `goal` is definitionally equal to
#        the generated `goal`.
#     3. Copies proof.lean into the per-test probe dir.
#     4. Runs `lake env lean` on proof.lean.
#     5. Replays harness-added checks:
#        - offline-goal outputs must provide `goal_closed : goal`;
#        - named proof theorems must not depend on `sorryAx` or
#          unallowlisted proof-local axioms.
#     6. Fails if elaboration errors, if proof.lean's own declarations
#        use `sorry`, or if the staged emitted file contains a forbidden
#        `sorry`. Raw generated files may contain only the standard
#        `theorem goal_holds := by sorry` emit-stage stub. Completed
#        outlines may contain no `sorry` at all.
#     7. Cleans up.
#
# Emission drift → import compile failure or completed-goal mismatch
# → loud test failure.

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
SAW-emitted goals or runs support-library proof regressions. It
cannot run without the Lean toolchain.

Install elan + the toolchain pinned in saw-core-lean/lean/lean-toolchain.
EOF
    exit 1
fi

# Locate the Lake project root and this test's probe dir.
# Test dirs live at otherTests/saw-core-lean/{proofs,support-lemmas}/<name>/,
# so the Lake project (saw-core-lean/lean/) is four levels up, and the
# saw-script root is also four levels up.
LAKE_DIR="$(cd ../../../../saw-core-lean/lean && pwd)"
SAW_DIR="$(cd ../../../.. && pwd)"
TEST_NAME="$(basename "$(pwd)")"

# shellcheck disable=SC1091
. "$(cd ../../support && pwd)/lake-timeout.sh"
PROBE_DIR="$LAKE_DIR/intTestsProbe/$TEST_NAME"

# Trust tier (2026-07-21, user decision). A row may carry a
# .trust-tier file naming a NON-STRICT trust tier; the only
# recognized value is `native-eval` (bv_decide rows: admits the
# per-invocation proof-local native axioms — see
# replay/axiom-audit.awk, the single authority for what each tier
# admits). The tier is per-row, printed loudly, and validated by
# the audit itself: unknown names and unused (stale) markers both
# fail. Strict rows pass no tier and are byte-identical to before.
TRUST_TIER=""
if [ -f .trust-tier ]; then
    TRUST_TIER="$(grep -v '^#' .trust-tier | head -n1 | tr -d '[:space:]')"
    if [ -z "$TRUST_TIER" ]; then
        echo "FAIL: .trust-tier exists but names no tier"
        exit 1
    fi
    echo "TRUST TIER: $TRUST_TIER (non-strict axiom tier; see replay/axiom-audit.awk)"
    echo "TRUST TIER RESOLUTION: migrate this row to the strict tier (swap bv_decide -> smt, delete .trust-tier) when lean-smt BV proof reconstruction lands upstream."
fi

# Axiom-declaration source lint (2026-07-21, introduced with the
# trust tiers and applied to ALL rows): proof-side files must never
# DECLARE axioms or reach machinery that can add declarations. The
# strict allowlist is exact-name so hand-rolled axioms cannot collide
# with it, but the native-eval tier admits a NAME PATTERN
# (declaration-dependent bv_decide axiom names), which a hand-declared
# axiom of a matching name could satisfy — `private axiom` names even
# print UNMANGLED in `#print axioms`. The shared lexer-based token
# lint (replay/proof-source-lint.awk, single authority with the
# replay trust kernel) tracks comments AND string/char literals
# (F1 fix — a comment-stripper without string awareness was blinded
# by a string containing the comment-open sequence) and bans every
# known escape hatch into environment mutation or kernel bypass.
SAW_DIR_EARLY="$(cd ../../../.. && pwd)"
for user_file in proof.lean completed.lean; do
    [ -f "$user_file" ] || continue
    # LC_ALL=C: the lint is a byte-level lexer (its non-ASCII taint
    # rule assumes byte mode), and UTF-8-locale awk can HARD-ERROR on
    # some multibyte input. A nonzero awk exit must reject even with
    # empty output — an awk crash must never read as a lint pass
    # (F1-fix hardening, 2026-07-21).
    bad_decl=$(LC_ALL=C awk -f "$SAW_DIR_EARLY/saw-core-lean/replay/proof-source-lint.awk" "$user_file" 2>&1) \
        && lint_rc=0 || lint_rc=$?
    if [ "$lint_rc" -ne 0 ] || [ -n "$bad_decl" ]; then
        echo "--- $user_file (proof-side files must not declare axioms or macro/elab machinery) ---"
        echo "$bad_decl"
        echo "(lint exit=$lint_rc)"
        echo "FAIL: axiom/macro declaration in proof-side file"
        exit 1
    fi
done

# source.txt (optional) names the SAW-emitted .lean file this
# test discharges, relative to the saw-script root. If present,
# it is copied into the probe dir as Emitted.lean so proof.lean
# can `import Emitted`. If completed.lean is present, the harness
# still checks source.txt points at an existing emitted file, but
# stages completed.lean instead; this models the edit-outline-and-
# replay workflow. If source.txt is absent, proof.lean is expected
# to be self-contained (no emitted goal).
EMITTED_ABS=""
EMITTED_REF_ABS=""
STAGED_EMITTED_ABS=""
USING_COMPLETED_OUTLINE=0
if [ -f source.txt ]; then
    EMITTED_REL=$(head -n1 source.txt)
    EMITTED_ABS="$SAW_DIR/$EMITTED_REL"
    EMITTED_REF_ABS="$EMITTED_ABS.good"
    if [ ! -f "$EMITTED_REF_ABS" ]; then
        echo "FAIL: tracked emitted file $EMITTED_REF_ABS not found"
        echo "Proof tests must use a tracked .lean.good artifact, not only an ignored stale .lean file."
        exit 1
    fi
    if [ -f "$EMITTED_ABS" ] && ! cmp -s "$EMITTED_ABS" "$EMITTED_REF_ABS"; then
        echo "FAIL: current emitted file $EMITTED_ABS differs from $EMITTED_REF_ABS"
        echo "Run the producing driver and refresh/review the golden before trusting this proof."
        exit 1
    fi
    if [ -f completed.lean ]; then
        STAGED_EMITTED_ABS="$(pwd)/completed.lean"
        USING_COMPLETED_OUTLINE=1
    else
        STAGED_EMITTED_ABS="$EMITTED_REF_ABS"
    fi
fi

mkdir -p "$PROBE_DIR"
if [ -n "$STAGED_EMITTED_ABS" ]; then
    cp "$STAGED_EMITTED_ABS" "$PROBE_DIR/Emitted.lean"
fi
cp proof.lean "$PROBE_DIR/proof.lean"

proof_targets() {
    # Audit hardening (2026-07-15): a proof row that closes its goal
    # via `lemma` (or `theorem`) must still get the #print axioms
    # audit; matching only `theorem` would let a lemma-based proof
    # skip the sorry/axiom check silently. (`example` is unnamed and
    # cannot be audited — the row structure requires named closers.)
    awk '
      /^[[:space:]]*(theorem|lemma)[[:space:]]+/ {
        name = $2
        sub(/:.*/, "", name)
        if (name != "") print name
      }
    ' "$PROBE_DIR/proof.lean"
}

goal_output_requires_goal_closed() {
    [ -n "$STAGED_EMITTED_ABS" ] && \
      grep -qE '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goal[[:space:]]*:' "$PROBE_DIR/Emitted.lean"
}

write_generated_probe() {
    awk '
      BEGIN { inserted = 0; saw_import = 0 }
      /^[[:space:]]*import[[:space:]]+/ {
        print
        saw_import = 1
        next
      }
      !inserted && saw_import {
        print ""
        print "namespace GeneratedHarness"
        inserted = 1
      }
      {
        print
      }
      END {
        if (!inserted) {
          print "namespace GeneratedHarness"
        }
        print ""
        print "end GeneratedHarness"
      }
    ' "$EMITTED_REF_ABS" > "$PROBE_DIR/Generated.lean"
}

audit_axioms() {
    # Single-checker principle (2026-07-18 hardening): the allowlist
    # audit is the SHARED authority in saw-core-lean/replay/
    # axiom-audit.awk — identical semantics with the product trust
    # kernel by mechanism, not discipline. (The former inline copy
    # also allowed SHORT axiom spellings — a hole, since probe files
    # have no opens and genuine axioms always print fully qualified;
    # removed from both consumers.) The row's trust tier (if any)
    # rides through here; the awk validates it (unknown/unused tiers
    # emit sentinel lines, which land in bad_axioms and fail).
    awk -v tier="$TRUST_TIER" -f "$SAW_DIR/saw-core-lean/replay/axiom-audit.awk"
}

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
if [ -n "$STAGED_EMITTED_ABS" ]; then
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
    if [ "$USING_COMPLETED_OUTLINE" -eq 1 ]; then
        bad_emitted_sorry=$(awk '
          /sorry/ {
            print FILENAME ":" FNR ":" $0
            bad = 1
          }
          END { exit bad }
        ' "$PROBE_DIR/Emitted.lean" 2>/dev/null || true)
    else
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
    fi
    if [ -n "$bad_emitted_sorry" ]; then
        echo "--- Emitted.lean (completed proof must not depend on sorry) ---"
        echo "$bad_emitted_sorry"
        echo "FAIL: emitted .lean contains unresolved proof obligations"
        rm -rf "$PROBE_DIR"
        exit 1
    fi
    if [ "$USING_COMPLETED_OUTLINE" -eq 1 ]; then
        write_generated_probe
        gen_build=$( ( cd "$LAKE_DIR" && $LAKE_TIMEOUT_CMD lake env lean \
                         -o "intTestsProbe/$TEST_NAME/Generated.olean" \
                         "intTestsProbe/$TEST_NAME/Generated.lean" ) 2>&1 ) && \
            gen_rc=0 || gen_rc=$?
        if [ "$gen_rc" -ne 0 ]; then
            echo "--- Generated.lean (tracked source artifact under harness namespace) ---"
            echo "$gen_build"
            echo "FAIL: tracked emitted .lean did not compile under completed-outline drift check"
            rm -rf "$PROBE_DIR"
            exit 1
        fi
        {
            echo "import Generated"
            echo "import Emitted"
            echo
            if grep -qE '^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+goal[[:space:]]*:' "$EMITTED_REF_ABS"; then
                echo "#check (show GeneratedHarness.goal = goal from rfl)"
            else
                # Module-artifact row (R3b): no `def goal` — drift-check
                # every top-level def instead, fully qualified through
                # its namespace. Same rfl discipline: the completed
                # outline may replace proof terms (proof irrelevance)
                # but must not change any definition's value.
                awk '
                  /^[[:space:]]*namespace[[:space:]]+/ { ns = $2; next }
                  /^[[:space:]]*end[[:space:]]+/ { ns = ""; next }
                  /^[[:space:]]*(noncomputable[[:space:]]+)?def[[:space:]]+/ {
                    name = ""
                    for (i = 1; i <= NF; i++) if ($i == "def") { name = $(i+1); break }
                    sub(/[:(].*/, "", name)
                    if (name != "") {
                      q = (ns != "" ? ns "." name : name)
                      print "#check (show GeneratedHarness." q " = " q " from rfl)"
                    }
                  }
                ' "$EMITTED_REF_ABS"
            fi
        } > "$PROBE_DIR/completed-outline.check.lean"
        # R3b review finding F2: an imports-only check file compiles
        # cleanly and would PASS with zero checks performed. The
        # drift gate must never be vacuous.
        if ! grep -q '^#check' "$PROBE_DIR/completed-outline.check.lean"; then
            echo "FAIL: completed-outline drift check emitted no #check lines"
            echo "(no 'def goal' and no extractable top-level defs in $EMITTED_REF_ABS)"
            rm -rf "$PROBE_DIR"
            exit 1
        fi
        drift_out=$( ( cd "$LAKE_DIR" && LEAN_PATH="intTestsProbe/$TEST_NAME" \
                       $LAKE_TIMEOUT_CMD lake env lean \
                        "intTestsProbe/$TEST_NAME/completed-outline.check.lean" ) 2>&1 ) && \
            drift_rc=0 || drift_rc=$?
        if [ "$drift_rc" -ne 0 ] || echo "$drift_out" | grep -qE "^[^[:space:]]+: error" ; then
            echo "--- completed-outline.check.lean (completed goal must match generated goal by rfl) ---"
            echo "$drift_out"
            echo "FAIL: completed.lean changes the generated proof obligation"
            rm -rf "$PROBE_DIR"
            exit 1
        fi
    fi
fi

# Elaborate proof.lean. LEAN_PATH points at the probe dir so
# `import Emitted` finds our freshly-built Emitted.olean.
proof_out=$( ( cd "$LAKE_DIR" && LEAN_PATH="intTestsProbe/$TEST_NAME" \
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
    check_file="$PROBE_DIR/proof.check.lean"
    cp "$PROBE_DIR/proof.lean" "$check_file"
    {
        echo
        echo "-- Harness-added prototype validation checks."
        # The axiom allowlist (axiom-audit.awk) matches EXACT fully
        # qualified names. proof.check.lean is a COPY of the row's
        # proof.lean, so any `open` there would otherwise abbreviate
        # the printed axiom names and fail the audit spuriously
        # (2026-07-19 finding: the 2026-07-18 hardening's "probe
        # files have no opens" premise is false for THIS consumer).
        echo "set_option pp.fullNames true"
        if goal_output_requires_goal_closed; then
            echo "#check (goal_closed : goal)"
            echo "#print axioms goal_closed"
        else
            proof_targets | while IFS= read -r target; do
                echo "#print axioms $target"
            done
        fi
    } >> "$check_file"

    check_out=$( ( cd "$LAKE_DIR" && LEAN_PATH="intTestsProbe/$TEST_NAME" \
                   $LAKE_TIMEOUT_CMD lake env lean \
                    "intTestsProbe/$TEST_NAME/proof.check.lean" ) 2>&1 ) && \
        check_rc=0 || check_rc=$?
    bad_axioms=$(printf '%s\n' "$check_out" | audit_axioms)
    # Vacuity guard (2026-07-20, pre-release audit backlog): the
    # allowlist audit passes when it finds NOTHING to reject, so an
    # audit that never ran must not look like a pass. Every appended
    # `#print axioms` line must produce exactly one audited-output
    # line ("depends on axioms" or "does not depend on any axioms"),
    # and there must be at least one — a row whose proof.lean names
    # no auditable closer (example-only / def-only) fails here
    # instead of silently skipping the sorry/axiom check.
    expected_audits=$(grep -c '^#print axioms ' "$check_file")
    actual_audits=$(printf '%s\n' "$check_out" \
        | grep -cE "depends on axioms|does not depend on any axioms")
    if [ "$expected_audits" -lt 1 ] || [ "$actual_audits" -ne "$expected_audits" ]; then
        echo "--- proof.check.lean (axiom audit) ---"
        echo "$check_out"
        echo "FAIL: axiom audit was vacuous (expected $expected_audits audited closer(s), saw $actual_audits audit line(s))"
        status=1
    elif [ "$check_rc" -ne 0 ] || echo "$check_out" | grep -qE "^[^[:space:]]+: error" ; then
        echo "--- proof.check.lean (harness-added checks) ---"
        echo "$check_out"
        echo "FAIL: proof theorem audit failed"
        status=1
    elif [ -n "$bad_axioms" ]; then
        echo "--- proof.check.lean (axiom audit) ---"
        echo "$check_out"
        echo "FAIL: proof theorem depends on unallowlisted axioms:"
        echo "$bad_axioms"
        status=1
    else
        echo "OK: proof.lean elaborated; checked theorem audit passed"
    fi
fi

rm -rf "$PROBE_DIR"
exit $status
