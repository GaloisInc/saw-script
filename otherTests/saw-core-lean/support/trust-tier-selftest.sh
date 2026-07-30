#!/usr/bin/env bash
# Trust-tier guard self-test (2026-07-21, introduced with the
# native-eval tier). Mutation tests for the tier machinery in
# lean-proof-test.sh + replay/axiom-audit.awk: each case stages a
# synthetic row that MUST FAIL with a specific diagnostic. A guard
# that stops firing is a silent trust hole (vacuity-guard doctrine:
# every guard ships with a mutation it demonstrably catches).
#
# Case groups:
#   End-to-end (via lean-proof-test.sh): stale-marker, unknown-tier,
#     missing-marker, axiom-decl-lint, private-axiom-decl,
#     prefixed-axiom-decl, string-hidden-axiom-decl (F1).
#   Pure-awk audit (axiom-audit.awk semantics on synthetic
#     `#print axioms` output): exact/tier accept, suffix/prefix
#     look-alikes, native-under-strict, sorry-under-tier,
#     noncanonical tier-pattern near-misses.
#   Pure lint (proof-source-lint.awk lexer semantics; narrowed to
#     the single `axiom` check 2026-07-30, D2): F1 string blindness,
#     the escaped-spelling boundary, cannot-classify rejections
#     (raw/interpolated strings, non-ASCII primes, ambiguous ]'),
#     and a no-false-positive acceptance of legitimate shapes.
#   Completed-outline binding, R-1 (via lean-proof-test.sh):
#     goal-less completed outline, harness-namespace capture.
#
# Invoked by test.sh (conformance and default test verbs). Stages
# rows under ../.tier-selftest/<case>/ so relative paths match real
# category rows; the staging dir is removed on every exit path.

set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
CATROOT="$(cd "$HERE/.." && pwd)"
STAGE="$CATROOT/.tier-selftest"

VERB="${1:-test}"
case "$VERB" in
    good) echo "trust-tier-selftest.sh: 'good' is a no-op"; exit 0 ;;
    clean) rm -rf "$STAGE"; exit 0 ;;
    test) ;;
    *) echo "trust-tier-selftest.sh: unknown verb '$VERB'" >&2; exit 1 ;;
esac

rm -rf "$STAGE"
mkdir -p "$STAGE"
trap 'rm -rf "$STAGE"' EXIT

status=0

# run_case <name> <required-diagnostic-substring>
# The synthetic row is expected to have been staged at $STAGE/<name>.
run_case() {
    local name="$1" want="$2" out rc
    out=$( cd "$STAGE/$name" && bash "$HERE/lean-proof-test.sh" test 2>&1 )
    rc=$?
    if [ "$rc" -eq 0 ]; then
        echo "FAIL[$name]: harness PASSED a row the tier guards must reject"
        echo "$out" | tail -5
        status=1
    elif ! printf '%s\n' "$out" | grep -qF "$want"; then
        echo "FAIL[$name]: harness failed, but WITHOUT the required diagnostic '$want'"
        echo "$out" | tail -10
        status=1
    else
        echo "OK[$name]: rejected with '$want'"
    fi
}

# Case 1: stale marker — tier declared, proof needs no tier axiom.
mkdir -p "$STAGE/stale-marker"
printf 'theorem tier_selftest_trivial : True := trivial\n' \
    > "$STAGE/stale-marker/proof.lean"
printf 'native-eval\n' > "$STAGE/stale-marker/.trust-tier"
run_case stale-marker "TRUST-TIER-UNUSED"

# Case 2: unknown tier name.
mkdir -p "$STAGE/unknown-tier"
printf 'theorem tier_selftest_trivial : True := trivial\n' \
    > "$STAGE/unknown-tier/proof.lean"
printf 'super-trusting\n' > "$STAGE/unknown-tier/.trust-tier"
run_case unknown-tier "UNKNOWN-TRUST-TIER"

# Case 3: bv_decide without a marker — strict allowlist must reject
# the per-invocation native axiom. The goal must actually reach the
# SAT/LRAT path (bv_normalize alone closes trivialities like
# x ^^^ x = 0 WITHOUT a native axiom — verified 2026-07-21);
# multiplication commutativity bitblasts for real.
mkdir -p "$STAGE/missing-marker"
cat > "$STAGE/missing-marker/proof.lean" <<'EOF'
import Std.Tactic.BVDecide
theorem tier_selftest_bv (x y : BitVec 8) : x * y = y * x := by bv_decide
EOF
run_case missing-marker "._native.bv_decide.ax_"

# Case 4: axiom declaration in a proof-side file — source lint fires
# even with a valid marker (this is the name-collision defense: a
# hand-declared axiom matching the tier's name pattern must never
# reach the audit).
mkdir -p "$STAGE/axiom-decl-lint"
cat > "$STAGE/axiom-decl-lint/proof.lean" <<'EOF'
axiom collide._native.bv_decide.ax_1 : False
theorem tier_selftest_collide : False := collide._native.bv_decide.ax_1
EOF
printf 'native-eval\n' > "$STAGE/axiom-decl-lint/.trust-tier"
run_case axiom-decl-lint "axiom declaration in proof-side file"

# Case 5 (2026-07-21 hardening pin): `private axiom` — the modifier
# prefix bypassed the original line-anchored lint, and a private
# axiom's name prints UNMANGLED in `#print axioms`, so before the
# hardening this matching-named axiom would have been ADMITTED on a tier row. The
# comment-aware token lint must reject it.
mkdir -p "$STAGE/private-axiom-decl"
cat > "$STAGE/private-axiom-decl/proof.lean" <<'EOF'
private axiom goal_holds._native.bv_decide.ax_1 : False
theorem tier_selftest_priv : False := goal_holds._native.bv_decide.ax_1
EOF
printf 'native-eval\n' > "$STAGE/private-axiom-decl/.trust-tier"
run_case private-axiom-decl "axiom declaration in proof-side file"

# Case 6 (2026-07-21 hardening pin): `set_option … in axiom` — a
# command prefix on the same line also bypassed the original lint.
mkdir -p "$STAGE/prefixed-axiom-decl"
cat > "$STAGE/prefixed-axiom-decl/proof.lean" <<'EOF'
set_option pp.fullNames true in axiom goal_closed._native.bv_decide.ax_1 : False
theorem tier_selftest_pref : False := goal_closed._native.bv_decide.ax_1
EOF
printf 'native-eval\n' > "$STAGE/prefixed-axiom-decl/.trust-tier"
run_case prefixed-axiom-decl "axiom declaration in proof-side file"

# Case 7 (F1 fix pin, 2026-07-21 soundness review): string-literal
# blindness — the original comment-stripping lint entered comment-skip
# mode inside a string containing the comment-open sequence and missed
# a following axiom declaration entirely (the axiom then matched the
# tier's name pattern and was admitted). The lexer-based lint tracks
# string literals and must flag the axiom.
mkdir -p "$STAGE/string-hidden-axiom-decl"
cat > "$STAGE/string-hidden-axiom-decl/proof.lean" <<'EOF'
def cmt : String := "/-"
axiom goal_holds._native.bv_decide.ax_1 : False
theorem tier_selftest_hidden : False := goal_holds._native.bv_decide.ax_1
EOF
printf 'native-eval\n' > "$STAGE/string-hidden-axiom-decl/.trust-tier"
run_case string-hidden-axiom-decl "axiom declaration in proof-side file"

# --- Pure-awk allowlist cases -------------------------------------
# The audit layer's own rejection semantics, exercised directly on
# synthetic `#print axioms` output (no Lean involved). These carry the
# exact-vs-suffix discipline pin at the layer that owns it: the
# end-to-end replay rows (saw-boundary/replay_reject_axiom,
# replay_reject_suffix_axiom) now fire at the earlier source-lint
# layer, so the awk's own discipline must be pinned here.

AWK_AUDIT="$(cd "$CATROOT/../../saw-core-lean/replay" && pwd)/axiom-audit.awk"

# awk_case <name> <tier> <axioms-csv> <want> ; want = "reject" | "pass"
awk_case() {
    local name="$1" tier="$2" axioms="$3" want="$4" out
    out=$(printf "'p' depends on axioms: [%s]\n" "$axioms" \
          | awk -v tier="$tier" -f "$AWK_AUDIT")
    case "$want" in
        reject)
            if [ -z "$out" ]; then
                echo "FAIL[awk:$name]: allowlist ACCEPTED axioms it must reject: $axioms (tier='$tier')"
                status=1
            else
                echo "OK[awk:$name]"
            fi ;;
        pass)
            if [ -n "$out" ]; then
                echo "FAIL[awk:$name]: allowlist rejected allowlisted axioms: $out"
                status=1
            else
                echo "OK[awk:$name]"
            fi ;;
    esac
}

# Exact allowlist accepted (strict).
awk_case exact-accept "" "propext, Classical.choice, Quot.sound, CryptolToLean.SAWCorePrimitives.vecToBitVec_bitVecToVec" pass
# The GENUINE tier shape accepted under the tier (goal_holds/goal_closed
# closers only — 2026-07-21 prefix pinning).
awk_case tier-accept "native-eval" "propext, goal_holds._native.bv_decide.ax_1_10, goal_closed._native.bv_decide.ax_2_5" pass
# Suffix-named look-alike rejected under BOTH tiers (review-finding pin).
awk_case suffix-strict "" "cheat_vecToBitVec_bitVecToVec" reject
awk_case suffix-tier "native-eval" "cheat_vecToBitVec_bitVecToVec, goal_holds._native.bv_decide.ax_1" reject
# Prefix-named look-alike rejected.
awk_case prefix-strict "" "propext_evil" reject
# bv_decide native axioms rejected under STRICT (tier gate is real).
awk_case native-strict "" "goal_holds._native.bv_decide.ax_1_10" reject
# sorryAx rejected even under the tier.
awk_case sorry-tier "native-eval" "sorryAx, goal_holds._native.bv_decide.ax_1" reject
# Non-canonical near-misses of the tier pattern rejected under the tier:
# wrong tactic family, and a non-sanctioned declaration prefix (the
# 2026-07-21 confirmed matching-name case — a private axiom named
# evil._native.bv_decide.ax_1 prints unmangled and matched the
# pre-hardening wildcard-prefix pattern).
awk_case noncanonical-family "native-eval" "goal_holds._native.native_decide.ax_1, goal_holds._native.bv_decide.ax_1" reject
awk_case noncanonical-prefix "native-eval" "evil._native.bv_decide.ax_1, goal_holds._native.bv_decide.ax_1" reject

# --- Pure lint cases ----------------------------------------------
# The source lint's own lexer semantics (proof-source-lint.awk),
# exercised directly on synthetic proof-side files. These pin the F1
# fix at the layer that owns it: the lexer must track string/char
# literals alongside comments, flag the one banned declaration form
# (`axiom` — the lint's single rule since the 2026-07-30 D2
# narrowing), preserve token boundaries across every elided
# construct, and reject loudly whatever it cannot classify with
# certainty against Lean's lexer.

AWK_LINT="$(cd "$CATROOT/../../saw-core-lean/replay" && pwd)/proof-source-lint.awk"

# lint_case <name> <want> [required-substring]
# want = "reject" | "accept"; file staged at $STAGE/lint-<name>.lean.
# Run under LC_ALL=C (byte mode) exactly as the consumers do.
lint_case() {
    local name="$1" want="$2" need="${3:-}" out rc
    out=$(LC_ALL=C awk -f "$AWK_LINT" "$STAGE/lint-$name.lean" 2>&1)
    rc=$?
    case "$want" in
        reject)
            if [ "$rc" -eq 0 ] && [ -z "$out" ]; then
                echo "FAIL[lint:$name]: lint PASSED a file it must reject"
                status=1
            elif [ -n "$need" ] && ! printf '%s\n' "$out" | grep -qF "$need"; then
                echo "FAIL[lint:$name]: rejected, but WITHOUT the required diagnostic '$need'"
                printf '%s\n' "$out" | head -3
                status=1
            else
                echo "OK[lint:$name]"
            fi ;;
        accept)
            if [ "$rc" -ne 0 ] || [ -n "$out" ]; then
                echo "FAIL[lint:$name]: lint rejected a legitimate proof-side file:"
                printf '%s\n' "$out" | head -3
                status=1
            else
                echo "OK[lint:$name]"
            fi ;;
    esac
}

# F1 at unit level: the hidden axiom line itself must be flagged.
cat > "$STAGE/lint-string-blind.lean" <<'EOF'
def cmt : String := "/-"
axiom sneaky : (1 : Nat) = 2
EOF
lint_case string-blind reject "axiom sneaky"

# RETIRED 2026-07-30 (D2 / plan 3a; decision log, residual-trust.md
# §Threat model): the escape-hatch ban cases — run-tac, hash-eval,
# run-meta, run-elab, hash-eval-bang, builtin-init, csimp,
# debug-option (F1-era), debug-plain, debug-escaped (A-6), notation,
# notation-local, infixl, syntax, export (A-1), attr-multiline,
# attr-multiline-gap (A-7). Their subjects were removed from the
# lint when it narrowed to the single `axiom` check: every one
# pinned a rule that defended against a deliberately-authored
# metaprogram, which the decided threat model puts out of scope, and
# K-1 (wave 3) showed the underlying denylist cannot be kept
# complete against the toolchain. These are probes whose question
# was withdrawn, not probes gone vacuous (the V-H1 class); the
# lexer-semantics and axiom-rule cases below are the surviving
# coverage.

# Constructs the byte-level lexer cannot certainly classify against
# Lean's lexer must reject loudly, never guess.
printf 'def r1 : String := r"x"\n' > "$STAGE/lint-raw-string.lean"
lint_case raw-string reject "raw string"
printf 'def i1 : String := s!"x"\n' > "$STAGE/lint-interp-string.lean"
lint_case interp-string reject "interpolated"
printf "def x := \xce\xb11' axiom evil : False\n" > "$STAGE/lint-nonascii-prime.lean"
lint_case nonascii-prime reject "non-ASCII"
printf "example (h' : 0 < 2) : zs[0]'h' = 1 := rfl\n" > "$STAGE/lint-ambiguous-idx.lean"
lint_case ambiguous-idx reject "ambiguous"

# END-block lexer-state guards (wave-4 DC-3: after the 17-row
# retirement these were the only lexer outcomes with no pin). The
# scanner must never reach EOF in literal/comment state silently —
# else every line after the opener was elided from the token scan
# and a hidden declaration would pass unseen (the F1 invariant the
# lint's own header states at :34-38).
printf 'def s : String := "oops\naxiom hidden : False\n' > "$STAGE/lint-unterm-string.lean"
lint_case unterm-string reject "unterminated string literal at EOF"
printf 'def pad : Nat := 1\n/- opened and never closed\naxiom hidden : False\n' > "$STAGE/lint-unterm-comment.lean"
lint_case unterm-comment reject "unterminated block comment at EOF"

# Legitimate proof-side shapes must stay accepted (no false
# positives): strings are data even when they contain banned words or
# comment delimiters; identifier primes; char literals with escapes;
# the checked-indexing proof operator; comments mentioning anything.
cat > "$STAGE/lint-ok-shapes.lean" <<'EOF'
/- a comment with " a quote and the word axiom
   nested /- axiom -/ still fine -/
-- line comment: axiom macro "
def s : String := " axiom macro /- -/ "
def v_1'''' : Nat := 3
def c : Char := '"'
def d : Char := '\''
def e : Char := '\x41'
example (h : 0 < 2) : bits[0]'h = bits[0]'(by omega) := rfl
theorem tier_ok : v_1'''' = 3 := rfl
EOF
lint_case ok-shapes accept

# Escaped-spelling acceptance boundary (kept through the 2026-07-30
# narrowing, with the 07-29 F8 measurement note carried forward):
# `«axiom»` is an ESCAPED IDENTIFIER, not the keyword — Lean would
# not parse it as a declaration — but under LC_ALL=C the guillemet
# bytes (\xc2\xab / \xc2\xbb) are non-letter boundaries, so the
# plain `axiom` rule matches it anyway. That is an over-REFUSAL, the
# safe direction, and this case pins that the behavior holds (a
# future "fix" that made the match Unicode-aware would flip this
# case, which is the moment to think rather than to adjust the pin).
printf '\xc2\xabaxiom\xc2\xbb evil : False\n' > "$STAGE/lint-axiom-escaped.lean"
lint_case axiom-escaped reject "axiom"

# Comment-glued axiom (task-#26 fix audit, 2026-07-30): a same-line
# block comment used to emit NOTHING into the stripped buffer
# (strings and char literals emit a space), so `1/- pad -/axiom …`
# glued the digit to the keyword and destroyed the left token
# boundary — a demonstrated false negative that admitted a
# tier-pattern axiom end-to-end. The lexer now leaves a separator
# for every elided construct; this case pins it (red-before: drop
# the `out = out " "` in the `/-` branch and this goes green-file).
printf 'def pad : Nat := 1/- pad -/axiom evil._native.bv_decide.ax_1 : False\n' \
    > "$STAGE/lint-comment-glued.lean"
lint_case comment-glued-axiom reject "axiom"

# No false positives: legitimate proof-side shapes that MENTION
# `axiom` (and former ban-list words) in comments or strings, plus
# ordinary attributes.
cat > "$STAGE/lint-newrules-ok.lean" <<'LINTOK'
-- a comment mentioning notation, syntax, export and implemented_by
/- and a block comment with axiom and «debug».skipKernelTC -/
def s : String := "notation syntax axiom unif_hint"
@[simp]
theorem fine : 1 + 1 = 2 := rfl
def prefixLength : Nat := 3
def my_export : Nat := 4
LINTOK
lint_case newrules-ok accept

# RK-5 (2026-07-24 second audit): the harness used to append its
# checks to a COPY of the row's proof.lean, so a row that omitted
# `import Emitted` and defined its OWN `goal` bound against itself and
# passed everything — an accidental-miss class (an honest row that
# forgets the import silently stops being checked) and the reason the
# suite could not catch an A-1/A-5-class regression. The checks now
# live in a separate probe module importing the tracked artifact.
R1_SOURCE_RK5='otherTests/saw-core-lean/workflows/offline_lean_e_series/test_offline_lean_e_series.E1_prove0.lean'
mkdir -p "$STAGE/decoy-goal"
printf '%s\n' "$R1_SOURCE_RK5" > "$STAGE/decoy-goal/source.txt"
cat > "$STAGE/decoy-goal/proof.lean" <<'DECOY'
import CryptolToLean

def goal : Prop := True

theorem goal_closed : goal := trivial
DECOY
run_case decoy-goal "environment already contains 'goal' from Emitted"

# Completed-outline binding guards (R-1 fix, 2026-07-24 audit):
# goal-presence is decided by the tracked reference artifact, and a
# completed outline that does not present the bare `def goal :` line
# must hard-fail — never silently skip the closer↔goal binding gate.
# Reuses a real tracked artifact path so the reference carries a
# genuine `def goal`.
R1_SOURCE='otherTests/saw-core-lean/workflows/cryptol_running_sum_verify/test_cryptol_running_sum_verify.eq_prove0.lean'
mkdir -p "$STAGE/unbound-completed"
printf '%s\n' "$R1_SOURCE" > "$STAGE/unbound-completed/source.txt"
printf 'import CryptolToLean\nabbrev goal : Prop := True\n' \
    > "$STAGE/unbound-completed/completed.lean"
printf 'import Emitted\ntheorem goal_closed : True := trivial\n' \
    > "$STAGE/unbound-completed/proof.lean"
run_case unbound-completed "does not present the emitted 'def goal :' line"

# The GeneratedHarness probe namespace is harness-internal; a user
# file that mentions it (the R-1 capture shape: planting a def the
# drift probe could resolve instead of the reference) is rejected on
# sight.
mkdir -p "$STAGE/harness-namespace-capture"
printf '%s\n' "$R1_SOURCE" > "$STAGE/harness-namespace-capture/source.txt"
printf 'import CryptolToLean\ndef goal : Prop := True\ndef GeneratedHarness.GeneratedHarness.goal : Prop := True\n' \
    > "$STAGE/harness-namespace-capture/completed.lean"
printf 'import Emitted\ntheorem goal_closed : True := trivial\n' \
    > "$STAGE/harness-namespace-capture/proof.lean"
run_case harness-namespace-capture "GeneratedHarness probe namespace"

if [ "$status" -eq 0 ]; then
    echo "trust-tier-selftest: ALL CASES OK"
fi
exit $status
