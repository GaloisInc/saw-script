#!/usr/bin/env bash
# run-tests.sh -- Build and lower the exception-lower test fixtures.
#
# Usage:
#   ./run-tests.sh              # compile + lower all fixtures
#   ./run-tests.sh --clean      # remove generated artifacts
#
# Requirements:
#   - clang++ (with -emit-llvm support)
#   - llvm-dis (optional, for inspecting output)
#   - ../build/exception-lower  (the lowering tool)
#
# This is a developer harness: it exercises the pass itself end-to-end on
# C++ inputs that contain real EH constructs.  The post-lowering shape is
# also exercised by the saw-script integration test
# `intTests/test_exception_lower/`, which does NOT depend on this script
# or on the tool being built.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TOOL="${SCRIPT_DIR}/../build/exception-lower"
CLANGXX="${CLANGXX:-clang++}"
LLVM_DIS="${LLVM_DIS:-llvm-dis}"

PASS=0
FAIL=0
SKIP=0

# Color output if terminal supports it.
if [ -t 1 ]; then
  GREEN='\033[0;32m'; RED='\033[0;31m'; YELLOW='\033[0;33m'; NC='\033[0m'
else
  GREEN=''; RED=''; YELLOW=''; NC=''
fi

pass() { echo -e "  ${GREEN}PASS${NC}: $1"; PASS=$((PASS + 1)); }
fail() { echo -e "  ${RED}FAIL${NC}: $1"; FAIL=$((FAIL + 1)); }
skip() { echo -e "  ${YELLOW}SKIP${NC}: $1"; SKIP=$((SKIP + 1)); }

# --- Clean mode ---
if [[ "${1:-}" == "--clean" ]]; then
  echo "Cleaning generated files..."
  rm -f "${SCRIPT_DIR}"/*.bc "${SCRIPT_DIR}"/*.ll
  echo "Done."
  exit 0
fi

# --- Check prerequisites ---
if ! command -v "$CLANGXX" &>/dev/null; then
  echo "ERROR: clang++ not found. Set CLANGXX env var." >&2
  exit 1
fi

TOOL_AVAILABLE=true
if [ ! -x "$TOOL" ]; then
  echo "WARNING: exception-lower tool not found at $TOOL"
  echo "         Compile-only mode (lowering steps will be skipped)."
  TOOL_AVAILABLE=false
fi

# --- Test files ---
TEST_FILES=(
  simple-throw.cpp
  nested-try-catch.cpp
  rethrow.cpp
  cross-function.cpp
)

echo "========================================"
echo " exception-lower integration tests"
echo "========================================"
echo ""

# --- Step 1: Compile each .cpp to bitcode ---
echo "--- Compiling to bitcode ---"
for src in "${TEST_FILES[@]}"; do
  bc="${src%.cpp}.bc"
  if "$CLANGXX" -emit-llvm -c -O0 -std=c++17 \
       -fno-exceptions-for-value-types \
       "${SCRIPT_DIR}/${src}" -o "${SCRIPT_DIR}/${bc}" 2>/dev/null; then
    # If the above flag is unsupported, retry without it.
    pass "compile ${src}"
  elif "$CLANGXX" -emit-llvm -c -O0 -std=c++17 \
       "${SCRIPT_DIR}/${src}" -o "${SCRIPT_DIR}/${bc}" 2>/dev/null; then
    pass "compile ${src}"
  else
    fail "compile ${src}"
  fi
done
echo ""

# --- Step 2: Run exception-lower on each ---
echo "--- Running exception-lower pass ---"
LOWER_FILES=(
  simple-throw.bc
  nested-try-catch.bc
  rethrow.bc
  cross-function.bc
)

for bc in "${LOWER_FILES[@]}"; do
  lowered="${bc%.bc}-lowered.bc"
  if [ "$TOOL_AVAILABLE" = true ]; then
    if "$TOOL" "${SCRIPT_DIR}/${bc}" -o "${SCRIPT_DIR}/${lowered}" 2>/dev/null; then
      pass "lower ${bc}"
    else
      fail "lower ${bc}"
    fi
  else
    skip "lower ${bc} (tool not built)"
  fi
done
echo ""

# --- Step 3: Optionally disassemble for inspection ---
echo "--- Disassembling lowered bitcode (if llvm-dis available) ---"
if command -v "$LLVM_DIS" &>/dev/null; then
  for bc in "${LOWER_FILES[@]}"; do
    lowered="${bc%.bc}-lowered.bc"
    ll="${bc%.bc}-lowered.ll"
    if [ -f "${SCRIPT_DIR}/${lowered}" ]; then
      if "$LLVM_DIS" "${SCRIPT_DIR}/${lowered}" -o "${SCRIPT_DIR}/${ll}" 2>/dev/null; then
        pass "disasm ${lowered}"
      else
        fail "disasm ${lowered}"
      fi
    fi
  done
else
  skip "llvm-dis not found; skipping disassembly"
fi
echo ""

# --- Step 4: SAW verification of lowered output is exercised by
#            intTests/test_exception_lower/ instead of this script.

# --- Summary ---
echo "========================================"
echo " Results: ${PASS} passed, ${FAIL} failed, ${SKIP} skipped"
echo "========================================"

if [ "$FAIL" -gt 0 ]; then
  exit 1
fi
exit 0
