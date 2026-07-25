#!/usr/bin/env bash
# doc-claim-lint.sh — every code identifier a MAINTAINED doc names must
# exist in the source tree.
#
# Category closure C2 (2026-07-24, from the second soundness audit's
# A-3): a soundness argument that rests on a named mechanism which was
# deleted or renamed is a claim with nothing behind it. A-3 was exactly
# that — `polymorphismResidual` is cited as a live translator-time
# refusal in architecture.md, README.md, contributing.md AND in
# `doc/2026-05-02_residual-trust.md`, the trust authority, where it
# backs the universe-soundness argument. It has not existed in the
# source since May. Two independent six-lane audits and a dedicated
# doc-faithfulness pass all read that sentence without checking the
# identifier resolved.
#
# This is the mechanical half of the category: an identifier either
# exists or it does not, and that is checkable. The half that stays
# human is a docstring or prose sentence asserting a code PROPERTY
# ("the proof argument is consumed") — see `saw_stream_realize`, whose
# docstring claims exactly that over a body that ignores it (S-1).
# Reviewers own that half; this script owns the names.
#
# THE CONVENTION THIS RELIES ON, and which it therefore enforces:
# in a maintained doc, `backticks` mean "this is a live identifier in
# this tree"; plain text does not. So a sentence CORRECTING a dead
# claim writes the dead name in plain text — as the A-3 corrections in
# architecture.md / README.md / residual-trust.md §3.4 now do. That is
# not a loophole: it is the distinction between citing a mechanism and
# naming one for the record, and it is what lets a doc describe its own
# history without the linter forcing the history out.
#
# SCOPE — deliberately narrow, and the narrowness is the point:
# only docs that make CURRENT claims are linted. A dated design,
# audit, plan or archive document is a historical record; it names
# what was live when it was written, and rewriting history to satisfy
# a linter would destroy the record. Those are excluded by name below.
#
# Usage: bash doc-claim-lint.sh [test|clean]

set -u

VERB="${1:-test}"
case "$VERB" in
    test) ;;
    good|clean) echo "doc-claim-lint.sh: '$VERB' is a no-op"; exit 0 ;;
    *) echo "doc-claim-lint.sh: unknown verb '$VERB'" >&2; exit 1 ;;
esac

SAW_DIR="$(cd "$(dirname "$0")/../../.." && pwd)"
CORE="$SAW_DIR/saw-core-lean"

# The MAINTAINED doc set: these describe the backend as it is today.
DOCS=(
    "$CORE/README.md"
    "$CORE/STATUS.md"
    # TODO.md is deliberately NOT linted: a backlog names things that
    # do not exist BY DESIGN — planned mechanisms, and (as with A-3)
    # missing ones it is filed to fix. Linting it would force the
    # bug report to stop naming the bug.
    "$CORE/doc/architecture.md"
    "$CORE/doc/contributing.md"
    "$CORE/doc/getting-started.md"
    "$CORE/doc/proof-cookbook.md"
    "$CORE/doc/2026-05-02_residual-trust.md"
    "$CORE/doc/2026-07-02_position-callee-calculus.md"
)

# Identifiers that legitimately do not resolve in the source tree.
# EVERY entry needs a reason; an unexplained entry is how a linter
# becomes theatre.
is_ignored() {
    case "$1" in
        # SAWCore/Cryptol surface syntax and SAWScript primitives are
        # named in docs but are not identifiers in THIS tree.
        parse_core|enable_experimental|prove_print|write_lean_term) return 0 ;;
        # Lean core / Mathlib names (not vendored here).
        Nat*|Vector*|BitVec*|Except*|Classical*) return 0 ;;
        # Lean core simp lemmas cited by the proof cookbook.
        reduceIte) return 0 ;;
        *) return 1 ;;
    esac
}

# Search scope: this checkout's real source, minus build output and
# vendored deps. saw-core / saw-central are included because the docs
# legitimately cite SAW-side names (errorOp, fixOp, …).
sources_contain() {
    # --exclude this script: its own header cites `polymorphismResidual`
    # as the motivating example, which otherwise makes the linter
    # evidence for the very claim it is meant to refute. (Caught by
    # running it: the A-3 identifier stopped being reported the moment
    # the support dir entered scope.)
    grep -rqF "$1" \
        --include="*.hs" --include="*.lean" --include="*.awk" \
        --include="*.sh" --include="*.sawcore" --include="*.cry" \
        --exclude="doc-claim-lint.sh" \
        "$SAW_DIR/saw-core-lean/src" \
        "$SAW_DIR/saw-core-lean/lean" \
        "$SAW_DIR/saw-core-lean/replay" \
        "$SAW_DIR/saw-core-lean/smoketest" \
        "$SAW_DIR/saw-central/src" \
        "$SAW_DIR/saw-core/src" \
        "$SAW_DIR/saw-core/prelude" \
        "$SAW_DIR/cryptol-saw-core/saw" \
        "$SAW_DIR/otherTests/saw-core-lean/support" \
        2>/dev/null
}

status=0
checked=0
missing=0

for doc in "${DOCS[@]}"; do
    [ -f "$doc" ] || { echo "FAIL: linted doc not found: $doc"; status=1; continue; }
    # Extract backticked spans, keep the ones SHAPED like a code
    # identifier this tree would define: camelCase with an interior
    # capital, or a saw_-prefixed Lean realization. Prose, tactics
    # (`rfl`, `omega`), file paths and shell lines do not match, which
    # is what keeps the false-positive rate low enough to be a gate.
    while IFS= read -r ident; do
        [ -n "$ident" ] || continue
        is_ignored "$ident" && continue
        checked=$((checked + 1))
        if ! sources_contain "$ident"; then
            echo "MISSING: \`$ident\` — named in $(basename "$doc"), not found in source"
            grep -n "\`$ident\`" "$doc" | head -2 | sed 's/^/    /'
            missing=$((missing + 1))
            status=1
        fi
    done < <(grep -o '`[^`]*`' "$doc" 2>/dev/null \
             | tr -d '`' \
             | grep -E '^([a-z][A-Za-z0-9_'"'"']{3,}|saw_[a-z_]{3,})$' \
             | grep -E '[A-Z]|^saw_' \
             | sort -u)
done

echo "doc-claim-lint: checked $checked doc-cited identifier(s) across ${#DOCS[@]} maintained docs"
if [ "$status" -eq 0 ]; then
    echo "doc-claim-lint: OK — every cited identifier resolves"
else
    echo "doc-claim-lint: $missing cited identifier(s) do NOT exist."
    echo "A maintained doc names a mechanism the source does not have."
    echo "Fix the DOC (or restore the mechanism) — do not add an ignore"
    echo "entry unless the name genuinely lives outside this tree."
fi
exit $status
