#!/usr/bin/env bash
#
# Emitted-Lean snapshot/diff oracle for the position-directed
# translation refactor (saw-core-lean/doc/2026-07-08_position-directed-
# translation-plan.md, Slice 0).
#
# Behavior-inert slices must leave the translator's output byte-
# identical. The test harness deletes stale artifacts and re-emits on
# every run, so the procedure is:
#
#   make conformance                                      # re-emit at baseline
#   bash support/emitted-lean-snapshot.sh snapshot .snapshots/baseline
#   ... apply a slice, rebuild saw ...
#   make conformance                                      # re-emit at HEAD
#   bash support/emitted-lean-snapshot.sh diff .snapshots/baseline
#
# "Emitted" = every *.lean file git does NOT track. Goldens
# (*.lean.good), differential/obligation observers (lean-observe.lean),
# proof probes (proof.lean), and shape probes (*.shouldfail.lean) are
# tracked sources; translator output is gitignored.
#
# diff exits nonzero on any difference and names the files; inspect
# with `diff -u <snapshot>/<file> <file>`. A behavioral slice uses the
# same procedure but REVIEWS the diff instead of requiring emptiness.

set -euo pipefail
cd "$(dirname "$0")/.."

mode=${1:?usage: emitted-lean-snapshot.sh snapshot|diff <dir>}
dir=${2:?usage: emitted-lean-snapshot.sh snapshot|diff <dir>}

emitted() {
  # Exclude the ENTIRE .snapshots tree, not just the baseline being
  # diffed: stored baselines (and retired ones under superseded/) are
  # frozen copies, not live emission. Before 2026-07-15 only "$dir"
  # was excluded, so cutting a new baseline swallowed every OTHER
  # baseline's copies and inflated the artifact count ~4x.
  comm -23 \
    <(find . -name '*.lean' -not -path './.elan/*' -not -path './.snapshots/*' \
        | sed 's|^\./||' | sort) \
    <(git ls-files '*.lean' | sort)
}

case "$mode" in
  snapshot)
    rm -rf "$dir"
    mkdir -p "$dir"
    emitted | while read -r f; do
      mkdir -p "$dir/$(dirname "$f")"
      cp "$f" "$dir/$f"
    done
    echo "snapshot: $(emitted | wc -l | tr -d ' ') emitted .lean files -> $dir"
    ;;
  diff)
    [ -d "$dir" ] || { echo "no snapshot at $dir" >&2; exit 2; }
    status=0
    while read -r f; do
      if [ ! -f "$dir/$f" ]; then
        echo "NEW (not in snapshot): $f"; status=1
      elif ! cmp -s "$dir/$f" "$f"; then
        echo "CHANGED: $f"; status=1
      fi
    done < <(emitted)
    while IFS= read -r -d '' f; do
      rel=${f#"$dir"/}
      if [ ! -f "$rel" ]; then
        echo "MISSING (in snapshot, not re-emitted): $rel"; status=1
      fi
    done < <(find "$dir" -name '*.lean' -print0)
    if [ "$status" -eq 0 ]; then
      echo "OK: emitted Lean identical to snapshot ($dir)"
    else
      echo "DIFF: emitted Lean differs from snapshot ($dir)"
    fi
    exit "$status"
    ;;
  *)
    echo "unknown mode: $mode" >&2
    exit 2
    ;;
esac
