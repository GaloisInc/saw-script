# Proof-side source lint — the SHARED authority used by both audit
# consumers (replay/lean-check-core.sh and
# otherTests/saw-core-lean/support/lean-proof-test.sh).
#
# Proof-side files (proof.lean / completed.lean) must never DECLARE
# axioms or reach any machinery that can add declarations to the
# environment: the strict allowlist is exact-name so hand axioms
# cannot collide with it, but the native-eval trust tier admits a
# NAME PATTERN (bv_decide's declaration-dependent native axioms),
# which a hand-declared axiom could satisfy by name. This lint is
# what makes the name-pattern admission sound: if no source path can
# declare a matching axiom, a residual tier-pattern axiom can only
# have come from a genuine bv_decide invocation.
#
# SOUNDNESS INVARIANT (F1 fix, 2026-07-21 review,
# doc/2026-07-21_soundness-review.md): the scanner must never be in
# literal/comment state while Lean's lexer is in code state — else a
# real declaration is hidden from the token scan. The original
# comment-stripper had no string awareness, so a string containing
# the comment-open sequence drove it into comment-skip mode over real
# code (F1, critical). This version is a character-level state
# machine over: nested block comments, line comments, plain string
# literals (escape-aware, multi-line), and char literals. Prime vs
# char-literal at `'` is decided by token tracking (`v_1'` continues
# an identifier; `1'a'` is a numeral then a char literal). Every
# construct where byte-level tracking cannot be CERTAIN to agree with
# Lean's lexer is rejected loudly instead of guessed:
#   - raw string literals (r"…", r#"…"#) — escapes differ
#   - interpolated strings (s!"…" etc.) — braces re-enter code
#   - `'` on a token containing non-ASCII characters — cannot decide
#     identifier-prime vs char literal without a Unicode table
#   - `]'X'` — after `]`, Lean resolves char-literal vs the
#     checked-indexing proof operator (`xs[i]'h`) by parser
#     backtracking (probed 2026-07-21: `zs[0]'h'` parses as the
#     notation, `fs[0]'"'` as a char-literal application); `]'` is
#     accepted as the operator only when the char-literal reading is
#     lexically impossible
#   - a quote in code position that opens no valid char literal
# This is sound because acceptance also requires the file to
# elaborate: a file our lexer tracks differently from Lean's is
# either rejected here or fails to compile (loud either way).
#
# Banned as standalone tokens wherever they appear in code: axiom,
# macro, macro_rules, elab, elab_rules, run_cmd, run_tac, run_meta,
# run_elab, initialize, builtin_initialize, attribute, any #eval
# spelling (#eval and #eval! — matched as a substring, since `#`
# cannot occur in identifiers after comment/string stripping); the
# extern / implemented_by / csimp attributes in any @[...] position;
# and any `debug.`-namespace option (debug.skipKernelTC suspends
# kernel checking of added declarations — the kernel is the trust
# anchor). This is the full set of core-Lean escape hatches into
# environment mutation or kernel bypass known as of the v4.32.0 bump
# (2026-07-22 re-review: run_meta / run_elab / #eval! added — all
# three exist as commands there, and the import-closure defense is
# NOT sufficient on its own because bv_decide rows import
# Std.Tactic.BVDecide, which transitively reaches Lean's meta layer).
# Earlier additions 2026-07-21 (F1 fix): run_tac / #eval /
# builtin_initialize / csimp / debug.* — run_tac can addDecl an axiom
# from inside a tactic block exactly the way bv_decide itself does,
# and csimp swaps implementations used by native evaluation, which
# the native-eval tier leans on.
# RE-REVIEW THIS LIST ON EVERY TOOLCHAIN BUMP.
# A comment or string literal may mention these words freely (string
# CONTENT is data — it is elided from the token scan).
#
# Output: one "<file>:<line>: <text>" per hit (goldens pin this
# format); exit 1 if any. Lexer-level rejections print a diagnostic
# message instead of the source line.

BEGIN { depth = 0; bad = 0; in_str = 0 }

function fatal(msg) {
  print FILENAME ":" FNR ": " msg
  bad = 1
  exit 1   # runs END, which exits with bad
}

{
  line = $0
  n = length(line)
  i = 1
  out = ""
  tok = 0   # 0=none, 1=identifier, 2=numeral, 3=contains-non-ASCII

  while (i <= n) {
    if (depth > 0) {
      two = substr(line, i, 2)
      if (two == "/-")      { depth++; i += 2 }
      else if (two == "-/") { depth--; i += 2 }
      else i++
      continue
    }
    if (in_str) {
      c = substr(line, i, 1)
      if (c == "\\")      i += 2          # escape (incl. gap at EOL)
      else if (c == "\"") { in_str = 0; i++ }
      else i++
      continue
    }

    c = substr(line, i, 1)
    two = substr(line, i, 2)

    if (two == "--") break                       # line comment
    if (two == "/-") { depth++; i += 2; tok = 0; continue }

    if (c == "\"") {
      # Raw string? token exactly `r` (+ optional #s) before the quote.
      p = i - 1
      while (p >= 1 && substr(line, p, 1) == "#") p--
      if (p >= 1 && substr(line, p, 1) == "r" &&
          (p == 1 || substr(line, p - 1, 1) !~ /[A-Za-z0-9_'!?]/))
        fatal("possible raw string literal — lint cannot verify; not permitted in proof-side files")
      if (i > 1 && substr(line, i - 1, 1) == "!")
        fatal("possible interpolated string literal — lint cannot verify; not permitted in proof-side files")
      in_str = 1
      out = out " "
      tok = 0
      i++
      continue
    }

    if (c == "'") {
      if (tok == 1) { out = out c; i++; continue }   # identifier prime
      if (tok == 3)
        fatal("prime/char-literal after a token containing non-ASCII characters — lint cannot classify; not permitted in proof-side files")
      # tok 0/2: char literal, or the checked-indexing proof operator
      # (`xs[i]'h`). Lean resolves `]'` by parser backtracking (probed
      # 2026-07-21: `zs[0]'h'` parses as the NOTATION even though 'h'
      # is a valid char literal, while `fs[0]'"'` parses as a CHAR
      # LITERAL application) — irreproducible at byte level, so:
      # after `]`, continue as code ONLY when the char-literal reading
      # is lexically impossible; reject every ambiguous sequence.
      shape = 0                    # closing quote within literal range?
      j = i + 1
      if (j <= n && substr(line, j, 1) == "\\") j += 2   # skip \ and the escaped char
      lim = j + 10
      while (j <= n && j <= lim) {
        if (substr(line, j, 1) == "'") { shape = j; break }
        j++
      }
      if (i > 1 && substr(line, i - 1, 1) == "]") {
        if (shape)
          fatal("quote after ] is ambiguous (checked-indexing proof vs char literal) — lint cannot classify; not permitted in proof-side files")
        out = out c                # indexing-proof operator
        tok = 0
        i++
        continue
      }
      if (!shape)
        fatal("cannot classify quote (no valid char literal here) — not permitted in proof-side files")
      i = shape + 1                # consume the char literal
      out = out " "
      tok = 0
      continue
    }

    # Ordinary code character: emit and track the token state.
    out = out c
    if (c ~ /[A-Za-z_]/)      { if (tok == 0) tok = 1 }
    else if (c ~ /[0-9]/)     { if (tok == 0) tok = 2 }
    else if (c == "!" || c == "?") { if (tok != 1 && tok != 3) tok = 0 }
    else if (c !~ /^[ -~\t]$/) tok = 3        # non-ASCII byte/char
    else tok = 0
    i++
  }

  # A-6 (2026-07-24 audit): Lean accepts ESCAPED name components, and
  # `«debug».skipKernelTC` is the same Name as `debug.skipKernelTC` —
  # so the denylist below, matching literal spellings, was evaded by
  # one pair of brackets, switching kernel type-checking off for the
  # whole file. Stripping the brackets before matching hardens EVERY
  # rule here at once (`«axiom»`, `«macro_rules»`, …), not just the
  # option rule that surfaced it.
  gsub(/[«»]/, "", out)

  # A-7 (2026-07-24 audit): the attribute rule is per-line BY
  # CONSTRUCTION, so an attribute split across lines —
  #     @[
  #       implemented_by evilImpl]
  # — was never matched. Carry an unclosed `@[` forward and match on
  # the joined text. `attr_pending` holds the text since the opening
  # bracket; it is cleared by the closing `]`, so an attribute list
  # spanning any number of lines is scanned as one string.
  scan = out
  if (attr_pending != "") {
    scan = attr_pending " " out
    if (out ~ /]/) attr_pending = ""
    else           attr_pending = scan
  } else if (out ~ /@\[/ && out !~ /@\[[^]]*]/) {
    attr_pending = out
  }

  # A-1 (2026-07-24 audit): syntax-declaring commands are banned.
  # `notation "goal" => True` in a proof file retargets the token
  # `goal` in EVERY importing module — including the checker's own
  # binding probe — so the closer proved `True` while the probe
  # type-checked against it. None of these has a legitimate place in
  # a discharge file, and this is the same defence-in-depth reasoning
  # that already bans `macro_rules` and `elab`, which are exactly
  # what `notation` desugars to. `unif_hint` is included as an
  # elaborator-level defeq extension (tested NOT exploitable against
  # the drift rfl on v4.32.0, but it belongs on the list). `export`
  # is included because it can introduce a competing root-level name.
  # Measured cost when added: ZERO — no current proof-side file in
  # the tree matches any of these outside comments, which the lint
  # already strips before matching.
  if (scan ~ /(^|[^A-Za-z0-9_'.])(axiom|macro|macro_rules|elab|elab_rules|run_cmd|run_tac|run_meta|run_elab|initialize|builtin_initialize|attribute|notation|syntax|infix|infixl|infixr|prefix|postfix|declare_syntax_cat|binder_predicate|unif_hint|export)([^A-Za-z0-9_'.]|$)/ ||
      scan ~ /#eval/ ||
      scan ~ /(^|[^A-Za-z0-9_'.])debug\.[A-Za-z]/ ||
      scan ~ /@\[[^]]*(extern|implemented_by|csimp)/) {
    print FILENAME ":" FNR ": " $0
    bad = 1
  }
}

END {
  if (bad == 0 && in_str)    { print FILENAME ": unterminated string literal at EOF"; bad = 1 }
  if (bad == 0 && depth > 0) { print FILENAME ": unterminated block comment at EOF"; bad = 1 }
  exit bad
}
