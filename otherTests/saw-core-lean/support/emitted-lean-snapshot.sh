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
#   make test                                             # re-emit at baseline
#   bash support/emitted-lean-snapshot.sh snapshot .snapshots/baseline
#   ... apply a slice, rebuild saw ...
#   make test                                             # re-emit at HEAD
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

mode=${1:?usage: emitted-lean-snapshot.sh snapshot|diff <dir>|selftest}
dir=${2:-}
if [ "$mode" != "selftest" ] && [ -z "$dir" ]; then
  echo "usage: emitted-lean-snapshot.sh snapshot|diff <dir>|selftest" >&2
  exit 2
fi

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
    # Freshness marker (F3, 0.02 release-gate audit, 2026-07-29). See
    # the `diff` mode below for why this exists.
    : > "$dir/.taken-at"
    echo "snapshot: $(emitted | wc -l | tr -d ' ') emitted .lean files -> $dir"
    ;;
  diff)
    [ -d "$dir" ] || { echo "no snapshot at $dir" >&2; exit 2; }
    status=0
    # STALENESS GUARD (F3, 0.02 release-gate audit, 2026-07-29).
    #
    # This oracle compares files on disk. It cannot tell a file that
    # was RE-EMITTED and matched from one that was never re-emitted at
    # all — and the two are worlds apart as evidence. The header above
    # says to re-emit with `make conformance`, which runs only
    # differential/obligations/saw-boundary; every drivers/, workflows/
    # and proofs/ artifact is then compared STALE-TO-STALE, i.e.
    # against itself. That is 187 of 354 files, and a "byte-identical
    # across all N artifacts" claim built on it is vacuous for more
    # than half its own corpus. It was cited that way for the
    # 2026-07-29 Term.hs split (the conclusion survived, because a full
    # `make test` run also covered it — but the attribution was wrong,
    # which is exactly the kind of evidence slippage this project
    # treats as a defect).
    #
    # So: every emitted file must be NEWER than the marker written when
    # the snapshot was taken. A file that is not was not re-emitted,
    # and comparing it proves nothing.
    if [ -f "$dir/.taken-at" ]; then
      stale=0
      while read -r f; do
        if [ ! "$f" -nt "$dir/.taken-at" ]; then
          [ "$stale" -lt 5 ] && echo "STALE (not re-emitted since snapshot): $f"
          stale=$((stale + 1))
        fi
      done < <(emitted)
      if [ "$stale" -gt 0 ]; then
        echo "STALE: $stale emitted file(s) were not re-emitted since the"
        echo "  snapshot was taken, so comparing them is vacuous. Re-emit with"
        echo "  \`make test\` (NOT \`make conformance\`, which re-emits only"
        echo "  differential/obligations/saw-boundary) and diff again."
        status=1
      fi
    else
      echo "no .taken-at marker in $dir — re-cut the snapshot; without it"
      echo "  this diff cannot tell re-emitted files from never-re-emitted ones"
      status=1
    fi
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
  selftest)
    # PIN for the staleness guard (F3). Cheap and exact: cut a
    # throwaway snapshot, then diff WITHOUT re-emitting anything. Every
    # file is by construction older than the marker, so the guard must
    # fire on all of them. Deleting the guard makes this report OK and
    # this case goes red.
    #
    # Deliberately NOT pinned with an emitter mutation: the natural
    # candidates also change a saw-boundary row, which `conformance`
    # DOES re-emit, so such a pin would go red for the wrong reason and
    # say nothing about staleness.
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    bash "$0" snapshot "$tmp/snap" >/dev/null
    out=$(bash "$0" diff "$tmp/snap" 2>&1) && rc=0 || rc=$?
    if [ "$rc" -eq 0 ]; then
      echo "FAIL[snapshot-oracle]: diff reported OK without any re-emission —"
      echo "  the staleness guard is not firing, so a 'byte-identical'"
      echo "  verdict can be produced by files nobody re-emitted."
      exit 1
    fi
    if ! printf '%s\n' "$out" | grep -q "were not re-emitted since the"; then
      echo "FAIL[snapshot-oracle]: diff failed, but NOT with the staleness"
      echo "  diagnostic — it must name staleness, not merely differ."
      printf '%s\n' "$out" | tail -4
      exit 1
    fi
    echo "OK[snapshot-oracle]: staleness guard fires when nothing was re-emitted"
    ;;
  *)
    echo "unknown mode: $mode" >&2
    exit 2
    ;;
esac
