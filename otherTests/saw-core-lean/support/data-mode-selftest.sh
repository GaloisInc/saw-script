#!/usr/bin/env bash
# data-mode-selftest.sh — SHIP-2 pin (wave-4, landed with the 0.02
# close-out arc, 2026-07-30).
#
# Exercises the data-files/XDG-cache branch of
# resolveLeanReplayAssets (saw-central/src/SAWCentral/Builtins.hs) —
# the branch every other harness bypasses, because
# lean-driver-test.sh defaults-and-exports SAW_LEAN_ROOT even when
# the caller left it unset. That blindness is how SHIP-1 (bindist
# missing the assets) survived three audit waves, and it left the
# SHIP-4 staging-race fix and the lean2- schema bump argued
# structurally rather than observed. This selftest is the
# wave-4 SHIP-2 verifier's one-off procedure made repeatable:
#
#   1. Build a synthetic install datadir containing EXACTLY the
#      files saw.cabal's data-files stanza declares (parsed +
#      glob-expanded here) — so a runtime-needed file missing from
#      the stanza fails HERE, not on a user's install.
#   2. Run the E1 replay goal (fixtures reused read-only from
#      proofs/E1_bvAdd_comm) with env -u SAW_LEAN_ROOT,
#      saw_datadir=<synthetic> (the Cabal Paths_saw env override),
#      and XDG_CACHE_HOME=<cache below>.
#   3. Assert: admission ("Lean kernel check passed"), a
#      .staged-ok marker under the CURRENT cache schema (lean2-*),
#      and NO old-schema (lean-*) dir was created.
#
# Cache persistence: XDG_CACHE_HOME points at the gitignored
# .data-mode-cache/ next to this suite, so steady-state local
# sweeps reuse a warm cache (~seconds); the cache re-stages cold
# whenever the shipped bytes change (the content fingerprint),
# which is exactly when staging needs re-observing. CI's fresh
# workspace is always cold. `clean` removes it.
#
# Requires $SAW (absolute path, same contract as the row harnesses).

set -u

VERB="${1:-test}"
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
CACHE="$HERE/../.data-mode-cache"

case "$VERB" in
    good) exit 0 ;;
    clean) rm -rf "$CACHE"; exit 0 ;;
    test) ;;
    *) echo "data-mode-selftest: unknown verb '$VERB'" >&2; exit 2 ;;
esac

if [ -z "${SAW:-}" ]; then
    echo "FAIL[data-mode]: SAW is not set (same contract as the row harnesses)"
    exit 1
fi

status=0
scratch="$(mktemp -d "${TMPDIR:-/tmp}/data-mode-selftest.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT
DATADIR="$scratch/datadir"
mkdir -p "$DATADIR" "$CACHE"

# 1. Synthetic datadir from the stanza (declared set, not the tree —
# the point is to test that what we DECLARE suffices at runtime).
( cd "$ROOT" &&
  awk '/^data-files:/{f=1;next} f && /^[[:space:]]*$/{exit} f{gsub(/^[[:space:]]+|[[:space:]]+$/,"");print}' \
      saw.cabal ) > "$scratch/stanza"
if [ ! -s "$scratch/stanza" ]; then
    echo "FAIL[data-mode]: could not parse the data-files stanza"
    exit 1
fi
while IFS= read -r entry; do
    # :(glob) = non-recursive, matching Cabal's data-files glob
    # semantics (step-1 fix audit F1, 2026-07-30): a bare git
    # pathspec globs recursively, which would stage subdirectory
    # files into the synthetic install that a real `cabal install`
    # would MISS — making this row green on a datadir no user can
    # have, which is the exact blindness it exists to close.
    ( cd "$ROOT" && git ls-files ":(glob)$entry" ) | while IFS= read -r f; do
        mkdir -p "$DATADIR/$(dirname "$f")"
        cp "$ROOT/$f" "$DATADIR/$f"
    done
done < "$scratch/stanza"
nfiles=$(find "$DATADIR" -type f | wc -l)
echo "OK[data-mode]: synthetic datadir staged ($nfiles declared files)"

# 2/3. The E1 replay goal against the synthetic install, TWICE
# (step-1 fix audit F3, 2026-07-30): the original single run against
# the persistent cache degraded after its first local pass to "does
# saw find an already-good cache dir" — the fingerprint covers
# shipped BYTES only, so a regression in the STAGING CODE (the
# SHIP-4 logic this row is billed as pinning) left the marker valid
# and was never re-observed. The COLD leg uses a per-run scratch
# XDG, so staging itself runs and is asserted on EVERY sweep
# (measured ~7.5s; a from-scratch lake build of the staged library
# is ~3.2s on this class of machine — the "few minutes" figure was
# the elan toolchain-download case, see getting-started.md). The
# WARM leg keeps the persistent cache and pins the marker-reuse
# path.
cat > "$scratch/test.saw" <<EOF
enable_experimental;
prove_print (offline_lean_replay "$ROOT/otherTests/saw-core-lean/proofs/E1_bvAdd_comm")
  {{ \\(x : [8]) (y : [8]) -> x + y == y + x }};
EOF

run_leg() {
    local xdg="$1" label="$2" rc=0 markers oldschema
    ( cd "$scratch" &&
      env -u SAW_LEAN_ROOT saw_datadir="$DATADIR" XDG_CACHE_HOME="$xdg" \
          timeout 900 "$SAW" test.saw ) > "$scratch/run-$label.log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ]; then
        echo "FAIL[data-mode:$label]: saw exited $rc on the data-files branch"
        tail -15 "$scratch/run-$label.log" | sed 's/^/  /'
        status=1
    elif ! grep -q "Lean kernel check passed" "$scratch/run-$label.log"; then
        echo "FAIL[data-mode:$label]: exit 0 but no 'Lean kernel check passed' line"
        tail -15 "$scratch/run-$label.log" | sed 's/^/  /'
        status=1
    else
        echo "OK[data-mode:$label]: E1 goal admitted through the data-files branch"
    fi
    markers=$(find "$xdg/saw-core-lean" -maxdepth 2 -name .staged-ok -path "*/lean2-*" 2>/dev/null | wc -l)
    if [ "$markers" -lt 1 ]; then
        echo "FAIL[data-mode:$label]: no .staged-ok marker under a lean2-* cache dir"
        find "$xdg" -maxdepth 3 2>/dev/null | sed 's/^/  /'
        status=1
    else
        echo "OK[data-mode:$label]: staged cache carries the lean2- schema marker"
    fi
    oldschema=$(find "$xdg/saw-core-lean" -maxdepth 1 -type d -name 'lean-*' 2>/dev/null | wc -l)
    if [ "$oldschema" -ne 0 ]; then
        echo "FAIL[data-mode:$label]: an old-schema lean-* cache dir was created"
        status=1
    fi
}

run_leg "$scratch/cold-xdg" cold
run_leg "$CACHE" warm

if [ "$status" -eq 0 ]; then
    echo "data-mode-selftest: ALL CHECKS OK"
fi
exit "$status"
