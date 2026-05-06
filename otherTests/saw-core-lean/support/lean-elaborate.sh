# lean-elaborate.sh — elaborate one or more generated Lean 4 files
# against the CryptolToLean Lake project that ships with saw-core-lean.
#
# Usage: bash ../support/lean-elaborate.sh FILE [FILE ...]
#
# Each FILE is a path (relative to the calling test directory) to a
# .lean file produced by SAW's Lean backend. The script copies it into
# saw-core-lean/lean/intTestsProbe/ so it can pick up the project's
# CryptolToLean import path, then runs `lake env lean` on it.
#
# Exit codes:
#   0  — every file elaborated cleanly (no errors; warnings allowed).
#   1  — at least one file produced a Lean elaboration error.
#   77 — `lake` is not on PATH; treat as "skip this elaboration step".
#        The caller should NOT propagate 77 as a test failure; instead
#        emit a one-line note to the test log and exit 0.
#
# We deliberately keep saw-core-lean/lean as the working Lake project
# rather than spinning a fresh one per test: lake's incremental build
# cache means subsequent invocations reuse the compiled
# CryptolToLean.* artifacts.

set -u

# Phase F (2026-05-04 audit): no environment-skips. If lake is not on
# PATH, every test that needs Lean elaboration fails loudly with a
# clear remediation message. CI on platforms that don't install elan
# must filter Lean tests off the platform deliberately, not rely on
# silent skip.
if ! command -v lake >/dev/null 2>&1; then
  echo "FAIL: lake is not on PATH (cannot elaborate Lean output)." >&2
  echo "  Install elan + the toolchain pinned in saw-core-lean/lean/lean-toolchain." >&2
  exit 1
fi

if [ "$#" -eq 0 ]; then
  echo "lean-elaborate.sh: no input files" >&2
  exit 1
fi

# Locate the saw-core-lean Lake project relative to this script.
# This script lives at otherTests/saw-core-lean/support/; the Lake
# project at saw-core-lean/lean/ is three levels up.
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LAKE_DIR="$SCRIPT_DIR/../../../saw-core-lean/lean"

# shellcheck disable=SC1091
. "$SCRIPT_DIR/lake-timeout.sh"

if [ ! -f "$LAKE_DIR/lakefile.toml" ]; then
  echo "lean-elaborate.sh: cannot find Lake project at $LAKE_DIR" >&2
  exit 1
fi

# Stage each file under a dedicated probe namespace so simultaneous
# tests don't collide. We use the calling test's basename plus the
# file's basename.
TEST_NAME="$(basename "$(pwd)")"
PROBE_DIR="$LAKE_DIR/intTestsProbe/$TEST_NAME"
mkdir -p "$PROBE_DIR"

# Track failures across all inputs but keep elaborating each one so
# the test log shows everything that broke at once.
status=0
for f in "$@"; do
  if [ ! -f "$f" ]; then
    echo "lean-elaborate.sh: $f does not exist" >&2
    status=1
    continue
  fi
  cp "$f" "$PROBE_DIR/$(basename "$f")"
done

# Make sure the project itself builds before probing — saves us from
# attributing a project-level error to a test file. A failure here
# means the saw-core-lean Lean support library does not compile —
# that's a real defect, not a "lake unavailable" environment skip.
# (Phase A audit, 2026-05-04: previous code exited 77 here, which
# the caller treated as a clean skip and silently masked broken
# library code. Now: exit 1 so it propagates as a test failure.)
set +e
build_log=$( ( cd "$LAKE_DIR" && $LAKE_TIMEOUT_CMD lake build ) 2>&1 )
build_rc=$?
set -e
if [ "$build_rc" -ne 0 ]; then
  echo "lean-elaborate.sh: lake build failed for $LAKE_DIR (rc=$build_rc)" >&2
  echo "$build_log" >&2
  rm -rf "$PROBE_DIR"
  exit 1
fi

for f in "$@"; do
  bn="$(basename "$f")"
  staged="$PROBE_DIR/$bn"
  if [ ! -f "$staged" ]; then
    continue
  fi
  echo "elaborating $bn"
  out=$( ( cd "$LAKE_DIR" && $LAKE_TIMEOUT_CMD lake env lean "intTestsProbe/$TEST_NAME/$bn" ) 2>&1 )
  rc=$?
  echo "$out"
  if [ "$rc" -ne 0 ] || echo "$out" | grep -E "^[^[:space:]]+: error" >/dev/null; then
    status=1
  fi
done

# Clean up staged copies.
rm -rf "$PROBE_DIR"

exit $status
