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
        ax != "CryptolToLean.SAWCorePrimitives.bitVecToVec_vecToBitVec") {
      print ax
    }
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
