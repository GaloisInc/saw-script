# lake-timeout.sh — picks a wall-clock guard for `lake build` and
# `lake env lean` invocations from the saw-core-lean test harnesses.
#
# Audit (2026-05-06): per-test timeout guard. P-1's reproducer
# (exponential translateTerm walk on shared subterms) consumed
# ~100 GB of RAM under a buggy translator before this audit;
# wrapping every Lean process in a 120-second cap limits the blast
# radius if a future regression brings back exponential behaviour
# at translation OR elaboration time.
#
# Exports:
#   LAKE_TIMEOUT_CMD  — the timeout invocation to prefix; expands
#                       to `timeout 120` (GNU coreutils on Linux),
#                       `gtimeout 120` (coreutils via brew on
#                       macOS), or empty (no timeout available;
#                       prints a one-line warning to stderr).
#
# Usage from a child script:
#   . "$(dirname "$0")/lake-timeout.sh"
#   $LAKE_TIMEOUT_CMD lake env lean foo.lean
#
# 120 seconds is generous for the test suite as it stands today
# (largest single elaboration is ~30 s on saw-core-lean's CI box)
# but tight enough that a runaway elaboration fails loud rather
# than holding up CI for the matrix's 60-minute limit.

LAKE_TIMEOUT_SECS="${LAKE_TIMEOUT_SECS:-120}"

if command -v timeout >/dev/null 2>&1; then
  LAKE_TIMEOUT_CMD="timeout ${LAKE_TIMEOUT_SECS}"
elif command -v gtimeout >/dev/null 2>&1; then
  LAKE_TIMEOUT_CMD="gtimeout ${LAKE_TIMEOUT_SECS}"
else
  echo "lake-timeout.sh: neither 'timeout' nor 'gtimeout' on PATH;" \
       "Lean processes will run unguarded." >&2
  LAKE_TIMEOUT_CMD=""
fi

export LAKE_TIMEOUT_CMD LAKE_TIMEOUT_SECS
