#!/usr/bin/env bash
# ship-list-check.sh — SHIP-3 closed check (wave-4, landed with the
# 0.02 close-out arc, 2026-07-30).
#
# The shipped-asset set is declared in saw.cabal's data-files stanza
# (a hand list with a NON-RECURSIVE `CryptolToLean/*.lean` glob),
# consumed at runtime by resolveLeanReplayAssets (Builtins.hs, which
# duplicates four top-level names in `relFiles`), and copied into
# the release bindist by .github/ci.sh bundle_files (derived via
# `git archive`). Wave 4 found the set exact at HEAD but maintained
# with no mechanical check — the enumeration-rot shape this project
# has been burned by. This script is the closed check:
#
#   (a) `CryptolToLean/` has no subdirectories (the non-recursive
#       glob's silent-miss precondition);
#   (b) the stanza, glob-expanded against tracked files, equals the
#       tracked runtime-asset set (git ls-files over
#       saw-core-lean/{lean,replay}, minus dev-only .gitignore);
#   (c) the four top-level names Builtins.hs hand-duplicates in
#       `relFiles` are present verbatim in the source;
#   (d) bundle_files still ships the trees (the W5-2 remedy — one
#       grep, so its silent removal fails here).
#
# Pure text/git; no saw, no lake. Fail-closed: any mismatch is a
# hard failure with the diff printed.

set -u

VERB="${1:-test}"
case "$VERB" in
    good|clean) exit 0 ;;
    test) ;;
    *) echo "ship-list-check: unknown verb '$VERB'" >&2; exit 2 ;;
esac

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
cd "$ROOT"

status=0
scratch="$(mktemp -d "${TMPDIR:-/tmp}/ship-list-check.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT

# (a) non-recursive glob precondition
subdirs="$(find saw-core-lean/lean/CryptolToLean -mindepth 1 -type d 2>/dev/null)"
if [ -n "$subdirs" ]; then
    echo "FAIL[ship-list]: CryptolToLean/ has subdirectories the non-recursive"
    echo "  data-files glob cannot ship:"
    printf '  %s\n' $subdirs
    status=1
else
    echo "OK[ship-list]: CryptolToLean/ has no subdirectories"
fi

# (b) stanza ≡ tracked runtime assets
awk '/^data-files:/{f=1;next} f && /^[[:space:]]*$/{exit} f{gsub(/^[[:space:]]+|[[:space:]]+$/,"");print}' \
    saw.cabal > "$scratch/stanza"
if [ ! -s "$scratch/stanza" ]; then
    echo "FAIL[ship-list]: could not parse a data-files stanza out of saw.cabal"
    status=1
fi
: > "$scratch/declared"
while IFS= read -r entry; do
    case "$entry" in
        *'*'*)
            # expand the glob against TRACKED files only, with
            # NON-RECURSIVE semantics — ":(glob)" pathspec magic
            # (step-1 fix audit F1/F2, 2026-07-30): bare git
            # pathspecs glob recursively, Cabal's data-files globs
            # do not, so a bare expansion would declare
            # subdirectory files cabal never ships and pass a check
            # cabal fails. With :(glob), a subdirectory .lean file
            # shows up ONLY on the tracked side of the diff below —
            # the check fails in the honest direction even without
            # the separate no-subdir precondition above.
            git ls-files ":(glob)$entry" >> "$scratch/declared"
            ;;
        *)  echo "$entry" >> "$scratch/declared" ;;
    esac
done < "$scratch/stanza"
sort -u "$scratch/declared" > "$scratch/declared.sorted"

git ls-files saw-core-lean/lean saw-core-lean/replay \
    | grep -v '/\.gitignore$' | sort -u > "$scratch/tracked"

if ! diff -u "$scratch/declared.sorted" "$scratch/tracked" > "$scratch/diff"; then
    echo "FAIL[ship-list]: saw.cabal data-files ≠ tracked runtime assets"
    echo "  (left = declared in saw.cabal, right = git ls-files minus .gitignore)"
    sed 's/^/  /' "$scratch/diff"
    status=1
else
    echo "OK[ship-list]: data-files stanza equals the tracked asset set ($(grep -c . "$scratch/tracked") files)"
fi

# every declared literal (non-glob) entry must exist on disk — a
# dead entry breaks `cabal sdist` loudly, but only when sdist runs,
# which CI does not; fail here instead.
while IFS= read -r entry; do
    case "$entry" in *'*'*) continue ;; esac
    if [ ! -f "$entry" ]; then
        echo "FAIL[ship-list]: declared data-file does not exist: $entry"
        status=1
    fi
done < "$scratch/stanza"

# (c) the relFiles hand-duplicates in Builtins.hs
for f in lakefile.toml lean-toolchain lake-manifest.json CryptolToLean.lean; do
    if ! grep -q "\"$f\"" saw-central/src/SAWCentral/Builtins.hs; then
        echo "FAIL[ship-list]: Builtins.hs relFiles no longer names \"$f\""
        status=1
    fi
done
[ "$status" -eq 0 ] && echo "OK[ship-list]: Builtins.hs relFiles names all four top-level assets"

# (d) the bindist still ships the trees (W5-2 remedy pin)
if ! grep -q 'git archive.*saw-core-lean/lean saw-core-lean/replay' .github/ci.sh; then
    echo "FAIL[ship-list]: .github/ci.sh bundle_files no longer ships saw-core-lean/{lean,replay}"
    status=1
else
    echo "OK[ship-list]: bundle_files ships the asset trees"
fi

# (e) toolchain pin equality (step-1 fix audit F6, 2026-07-30): the
# pins converged the same day this check landed, and the convergence
# retired the doc warnings that were the previous human guard — so
# this equality is now the ONLY thing standing between the tree and
# a recurrence of the destructive shared-library clobber (a path-dep
# project building the shared library in place at a mismatched pin).
if [ "$(cat examples/saw-lean/proof/lean-toolchain)" \
     != "$(cat saw-core-lean/lean/lean-toolchain)" ]; then
    echo "FAIL[ship-list]: demo/library lean-toolchain pins have diverged:"
    echo "  demo:    $(cat examples/saw-lean/proof/lean-toolchain)"
    echo "  library: $(cat saw-core-lean/lean/lean-toolchain)"
    echo "  (bump BOTH in one commit — see examples/saw-lean/README.md Step 3)"
    status=1
else
    echo "OK[ship-list]: demo and library toolchain pins agree"
fi

if [ "$status" -eq 0 ]; then
    echo "ship-list-check: ALL CHECKS OK"
fi
exit "$status"
