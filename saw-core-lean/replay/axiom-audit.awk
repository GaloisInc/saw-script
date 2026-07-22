# THE axiom-allowlist audit — the SINGLE authority shared by the
# product trust kernel (replay/lean-check-core.sh) and the CI proof
# harness (otherTests/saw-core-lean/support/lean-proof-test.sh).
# Parses `#print axioms` output ("‘X’ depends on axioms: [...]",
# including multi-line bracket lists) and prints every
# NON-allowlisted axiom (empty output = pass).
#
# EXACT match against the fixed allowlist — never suffix/regex (a
# suffix match would admit e.g. unsound_vecToBitVec_bitVecToVec;
# 2026-07-16 review finding). FULL names only: both consumers'
# probe files contain no `open` commands, so the genuine support
# axioms always print fully qualified — the formerly-allowed short
# spellings could only ever match a user-declared TOP-LEVEL axiom
# of the same bare name and were a hole (2026-07-18 hardening
# finding; removed from both consumers simultaneously).
#
# TRUST TIERS (2026-07-21, user decision): pass -v tier=<name> to
# admit a tier's additional axioms for THIS row only. Recognized:
#   (unset/empty)  — STRICT: the fixed allowlist above, nothing else.
#   native-eval    — additionally admits bv_decide's per-invocation
#                    proof-local native axioms, which on this
#                    toolchain print as <decl>._native.bv_decide.ax_N*
#                    (declaration-dependent names, so this is the ONE
#                    PATTERN rule; both consumers pair it with a source
#                    lint — proof-source-lint.awk — forbidding
#                    axiom/macro/elab declarations in proof-side files,
#                    so a hand-declared axiom cannot collide with the
#                    pattern by name. This name-collision risk is why
#                    bare patterns are not acceptable for the strict
#                    list). 2026-07-21 hardening: the <decl> prefix is
#                    pinned to the sanctioned closer names
#                    goal_holds/goal_closed — every tier row discharges
#                    through those (harness-enforced). A future tier row
#                    whose closer has another name fails LOUD here;
#                    extend deliberately, never widen to a bare
#                    wildcard.
#                    KNOWN GAP (F1, 2026-07-21 soundness review,
#                    doc/2026-07-21_soundness-review.md): the source
#                    lint is not yet string-literal aware, so it can
#                    miss a hand-declared axiom hidden after a string
#                    containing the comment-open sequence. Until F1 is
#                    fixed, the name-collision defense is incomplete;
#                    the tier is safe only because all current tier
#                    rows are first-party and inspected.
# Any other tier value fails loudly (UNKNOWN-TRUST-TIER sentinel).
# A declared tier whose extra axioms never appear fails loudly too
# (TRUST-TIER-UNUSED sentinel) — a tier marker must never be a
# no-op, else stale markers accumulate silent trust.
function tier_allows(ax) {
  if (tier == "native-eval" &&
      ax ~ /^goal_(holds|closed)\._native\.bv_decide\.ax_[0-9_]+$/) {
    tier_used = 1
    return 1
  }
  return 0
}
function check(line,    n, xs, i, ax) {
  sub(/^.*depends on axioms: \[/, "", line)
  sub(/\].*$/, "", line)
  n = split(line, xs, /,[[:space:]]*/)
  for (i = 1; i <= n; i++) {
    ax = xs[i]
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", ax)
    if (ax != "" &&
        ax != "propext" &&
        ax != "Classical.choice" &&
        ax != "Quot.sound" &&
        ax != "CryptolToLean.SAWCorePrimitives.vecToBitVec_bitVecToVec" &&
        ax != "CryptolToLean.SAWCorePrimitives.bitVecToVec_vecToBitVec" &&
        !tier_allows(ax)) {
      print ax
    }
  }
}
BEGIN {
  if (tier != "" && tier != "native-eval") {
    print "UNKNOWN-TRUST-TIER: " tier
    tier = ""
  }
}
END {
  if (tier == "native-eval" && !tier_used) {
    print "TRUST-TIER-UNUSED: native-eval (no bv_decide native axiom in any audited closer — remove the stale .trust-tier marker)"
  }
}
/depends on axioms:/ {
  pending = $0
  if (pending ~ /\]/) { check(pending); pending = "" }
  else collecting = 1
  next
}
collecting {
  pending = pending " " $0
  if ($0 ~ /\]/) { check(pending); pending = ""; collecting = 0 }
}
