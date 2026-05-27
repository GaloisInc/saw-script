#!/usr/bin/env bash
# test.sh -- IR-structure regression tests for the exception-lower pass.
#
# These tests run the pass directly on hand-written `.ll` fixtures and
# check post-lowering invariants of the transformed IR, complementing
# the SAW-level behavioural test in ../test_exception_lower/.
#
# Required tools:
#   * exception-lower  (built from saw-tools/exception-lower)
#   * opt              (LLVM)
#   * llvm-dis         (LLVM)
#
# Lookup order for the pass binary:
#   1. $EXCEPTION_LOWER
#   2. exception-lower on $PATH
#   3. ../../saw-tools/exception-lower/build*/exception-lower
#
# If any required tool is missing, the test prints a "SKIP" message
# and exits 0.  The SAW integration-test driver treats exit 0 as
# success, so CI environments that do not yet build the C++ pass will
# not be blocked.

set -u
set -o pipefail

skip() {
    echo "SKIP test_exception_lower_ir: $*"
    exit 0
}

fail() {
    echo "FAIL test_exception_lower_ir: $*"
    exit 1
}

# Resolve the pass binary.
if [ "${EXCEPTION_LOWER:-}" != "" ]; then
    EXCLOW="$EXCEPTION_LOWER"
elif command -v exception-lower >/dev/null 2>&1; then
    EXCLOW=$(command -v exception-lower)
else
    EXCLOW=$(find ../../saw-tools/exception-lower -maxdepth 3 \
                  -type f -name exception-lower 2>/dev/null | head -1 || true)
fi
if [ -z "${EXCLOW:-}" ] || [ ! -x "$EXCLOW" ]; then
    skip "exception-lower binary not found"
fi

# Resolve opt / llvm-dis (allow versioned names like opt-18).
find_tool() {
    local base="$1"
    if command -v "$base" >/dev/null 2>&1; then
        command -v "$base"
        return
    fi
    local cand
    for cand in "$base"-21 "$base"-20 "$base"-19 "$base"-18 "$base"-17 "$base"-16 "$base"-15 "$base"-14; do
        if command -v "$cand" >/dev/null 2>&1; then
            command -v "$cand"
            return
        fi
    done
    echo ""
}
OPT=$(find_tool opt)
LLVMDIS=$(find_tool llvm-dis)
if [ -z "$OPT" ] || [ -z "$LLVMDIS" ]; then
    skip "opt or llvm-dis not found on PATH"
fi

echo "Using exception-lower: $EXCLOW"
echo "Using opt:             $OPT"
echo "Using llvm-dis:        $LLVMDIS"

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

run_pass() {
    local input="$1"
    local lowered="$TMP/$(basename "$input" .ll).lowered.bc"
    local disasm="$TMP/$(basename "$input" .ll).lowered.ll"
    if ! "$EXCLOW" "$input" -o "$lowered" >&2; then
        fail "exception-lower failed on $input"
    fi
    if ! "$OPT" -passes=verify "$lowered" -o /dev/null >&2; then
        fail "opt -passes=verify rejected lowered $input"
    fi
    if ! "$LLVMDIS" "$lowered" -o "$disasm" >&2; then
        fail "llvm-dis failed on lowered $input"
    fi
    echo "$disasm"
}

assert_absent() {
    local label="$1"; local file="$2"; local pat="$3"
    if grep -qE "$pat" "$file"; then
        echo "--- offending IR ($label) ---"
        cat "$file"
        echo "----------------------------"
        fail "$label: pattern unexpectedly present: $pat"
    fi
}

assert_present() {
    local label="$1"; local file="$2"; local pat="$3"
    if ! grep -qE "$pat" "$file"; then
        echo "--- offending IR ($label) ---"
        cat "$file"
        echo "----------------------------"
        fail "$label: pattern expected but missing: $pat"
    fi
}

# Grep patterns are tight enough to ignore the `source_filename =` line
# (which echoes the fixture name and so contains "landingpad" /
# "unreachable" as substrings) and to ignore residual `declare` lines
# for runtime functions whose calls were removed.

echo "=== phi_before_landingpad ==="
PHI_LL=$(run_pass phi_before_landingpad.ll) || exit 1
# Core fix: invoke + landingpad instructions must be gone.
assert_absent "phi_before_landingpad" "$PHI_LL" '^[[:space:]]+invoke[[:space:]]'
assert_absent "phi_before_landingpad" "$PHI_LL" '=[[:space:]]landingpad[[:space:]]'
# The PHI must survive, but its incoming labels must reference the
# synthesized `.ehcheck` blocks rather than the original invoke blocks.
assert_present "phi_before_landingpad" "$PHI_LL" '=[[:space:]]phi[[:space:]]i32.*ehcheck.*ehcheck'
assert_absent  "phi_before_landingpad" "$PHI_LL" 'phi i32 \[ i32 1, %first \]'
echo "  ok"

echo "=== throw_then_unreachable ==="
THROW_LL=$(run_pass throw_then_unreachable.ll) || exit 1
# Only assert that __cxa_ runtime *calls* are gone; declarations may
# linger as zero-use externs and are harmless to verification.
assert_absent "throw_then_unreachable" "$THROW_LL" '^[[:space:]]+(call|invoke)[^\n]*@__cxa_'
assert_absent "throw_then_unreachable" "$THROW_LL" '^[[:space:]]+unreachable([[:space:]]|$)'
assert_present "throw_then_unreachable" "$THROW_LL" '^[[:space:]]+ret[[:space:]]+i32'
echo "  ok"

echo "=== rethrow ==="
RETHROW_LL=$(run_pass rethrow.ll) || exit 1
assert_absent "rethrow" "$RETHROW_LL" '^[[:space:]]+(call|invoke)[^\n]*@__cxa_rethrow'
assert_absent "rethrow" "$RETHROW_LL" '^[[:space:]]+unreachable([[:space:]]|$)'
assert_present "rethrow" "$RETHROW_LL" '^[[:space:]]+ret[[:space:]]+void'
echo "  ok"

echo "=== test_exception_lower_ir OK ==="
