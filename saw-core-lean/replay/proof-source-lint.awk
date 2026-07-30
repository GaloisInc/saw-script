# Proof-side source lint — the SHARED authority used by both audit
# consumers (replay/lean-check-core.sh and
# otherTests/saw-core-lean/support/lean-proof-test.sh).
#
# ONE CHECK, deliberately (D2 / plan 3a, decided 2026-07-30 —
# decision log; threat model: doc/2026-05-02_residual-trust.md
# §Threat model): a proof-side file (proof.lean / completed.lean)
# must not contain an `axiom` declaration.
#
# Why this one check is CLOSED where the previous 22-command
# denylist was not: the strict trust tier's axiom audit exact-matches
# five fully-qualified names, so a hand-declared axiom cannot collide
# with it (a namespaced duplicate has a different fully-qualified
# name). Only the native-eval tier's NAME-PATTERN admission
# (bv_decide's declaration-dependent native axioms) needs the
# guarantee "no source path can declare a matching axiom" — and
# `axiom` is the only surface declaration form that mints an axiom.
# If no `axiom` keyword appears, a residual tier-pattern axiom can
# only have come from a genuine bv_decide invocation.
#
# What this lint deliberately does NOT do (was: a denylist of
# macro/elab/run_*/notation/#eval/attribute/option escape hatches):
# defend against an adversarial proof author. Lean elaboration
# executes user code, and the wave-3 audit (K-1) demonstrated that a
# denylist of command heads cannot be kept complete against the
# toolchain — `simproc` was missing after two hand re-reviews. Under
# the decided threat model that author is out of scope; the checks
# that remain load-bearing against them do not exist, and users are
# told so (README: "What the replay checks defend against"). The
# kernel-checked binding theorem, the axiom audit, the drift
# binding, and the staged-digest re-verification are the checks this
# lint backstops, not replaces.
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
# The lexer is kept VERBATIM from the pre-narrowing lint: it was
# hardened once (F1) and has been defect-free since, while every
# later defect in this file (A-6, A-7, K-1) was in the rules — so
# the rules shrank and the machine did not change.
#
# `axiom` is matched as a standalone token wherever it appears in
# code — Lean only accepts it at command position, so matching more
# widely can only over-refuse (e.g. the escaped identifier
# `«axiom»`, which is NOT the keyword, still trips the byte-level
# boundary match). Refusal is the safe direction, and a comment or
# string literal may mention the word freely (string CONTENT is data
# — it is elided from the token scan).
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

  if (out ~ /(^|[^A-Za-z0-9_'.])axiom([^A-Za-z0-9_'.]|$)/) {
    print FILENAME ":" FNR ": " $0
    bad = 1
  }
}

END {
  if (bad == 0 && in_str)    { print FILENAME ": unterminated string literal at EOF"; bad = 1 }
  if (bad == 0 && depth > 0) { print FILENAME ": unterminated block comment at EOF"; bad = 1 }
  exit bad
}
