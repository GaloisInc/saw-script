# Proof-side source lint — the SHARED authority used by both audit
# consumers (replay/lean-check-core.sh and
# otherTests/saw-core-lean/support/lean-proof-test.sh).
#
# Proof-side files (proof.lean / completed.lean) must never DECLARE
# axioms or macro/elab-level machinery: the strict allowlist is
# exact-name so hand axioms cannot collide with it, but the
# native-eval trust tier admits a NAME PATTERN (bv_decide's
# declaration-dependent native axioms), which a hand-declared axiom
# could satisfy by name. 2026-07-21 hardening: the original line-anchored
# keyword grep was bypassable by modifier/command prefixes on the
# same line (`private axiom …`, `set_option … in axiom …`,
# `@[simp] axiom …`) — a private axiom's name even PRINTS unmangled
# in `#print axioms`, so the matching-named axiom would have been admitted on a
# tier row. This lint therefore strips comments (line `--` and
# NESTED block `/- -/`) and then flags the banned keywords as
# standalone tokens ANYWHERE in the remaining source text.
#
# Banned as commands wherever they appear: axiom, macro, macro_rules,
# elab, elab_rules, run_cmd, initialize, attribute; plus the
# extern / implemented_by attributes in any @[...] position.
# A comment may mention these words freely; code may not contain the
# tokens at all (a string literal containing one fails loudly — cheap
# to reword, and keeps the lint un-foolable).
#
# Output: one "<file>:<line>: <text>" per hit; exit 1 if any.

BEGIN { depth = 0; bad = 0 }
{
  line = $0
  out = ""
  while (length(line) > 0) {
    if (depth > 0) {
      open_i  = index(line, "/-")
      close_i = index(line, "-/")
      if (open_i > 0 && (close_i == 0 || open_i < close_i)) {
        depth++
        line = substr(line, open_i + 2)
        continue
      }
      if (close_i > 0) {
        depth--
        line = substr(line, close_i + 2)
        continue
      }
      line = ""
    } else {
      open_i = index(line, "/-")
      dash_i = index(line, "--")
      if (open_i > 0 && (dash_i == 0 || open_i < dash_i)) {
        out = out substr(line, 1, open_i - 1)
        depth++
        line = substr(line, open_i + 2)
        continue
      }
      if (dash_i > 0) {
        out = out substr(line, 1, dash_i - 1)
        line = ""
        continue
      }
      out = out line
      line = ""
    }
  }
  if (out ~ /(^|[^A-Za-z0-9_'.])(axiom|macro|macro_rules|elab|elab_rules|run_cmd|initialize|attribute)([^A-Za-z0-9_'.]|$)/ ||
      out ~ /@\[[^]]*(extern|implemented_by)/) {
    print FILENAME ":" FNR ": " $0
    bad = 1
  }
}
END { exit bad }
