#!/usr/bin/env bash
# replay-kernel-selftest.sh — mutation tests for the REPLAY TRUST
# KERNEL's own named guards (saw-core-lean/replay/lean-check-core.sh).
#
# Category closure C4 (2026-07-24). The project rule "every guard
# ships with a mutation it demonstrably catches" existed as a
# CONVENTION and was not enforced — so it rotted. Enumerating the
# kernel's 25 named failures against the corpus found only FOUR with
# any mutation pinning them, and the unpinned 21 included the two
# guards the second audit's criticals defeat:
#
#   closer-wrong-type       ← what A-5 defeats (coercion + hidden def)
#   completed-outline-drift ← what S-1 defeats (erasable obligation)
#
# A guard nobody has watched fire is where the next hole lives. That
# makes this predictive, not hygienic.
#
# It also covers this project's own recent work honestly: the A-2 fix
# (replay-emission-missing-goal-def) and half the R-1 fix
# (authority-missing-goal-def, and the KERNEL spelling of
# harness-namespace-in-user-file — the R-1 commit pinned only the CI
# harness's spelling) shipped with no mutation at all.
#
# These drive lean-check-core.sh DIRECTLY with synthetic stages, so
# they pin the kernel rather than a consumer of it. Cost: each case
# runs real Lean; `lake build` is cached across cases.
#
# Usage: bash replay-kernel-selftest.sh [test|clean]

set -u

VERB="${1:-test}"
HERE="$(cd "$(dirname "$0")" && pwd)"
SAW_DIR="$(cd "$HERE/../../.." && pwd)"
PROJ="$SAW_DIR/saw-core-lean/lean"
CORE="$SAW_DIR/saw-core-lean/replay/lean-check-core.sh"
STAGE_ROOT="${TMPDIR:-/tmp}/saw-lean-kernel-selftest.$$"
# The clean verb removes ALL runs' stage roots, not this shell's:
# `$$` of a cleaning invocation is by construction a different PID
# from the run that created a directory, so `rm -rf "$STAGE_ROOT"`
# could never remove anything (wave-5 DC5-4 — the verb had been a
# no-op since it was written). The test verb still uses the
# PID-unique root so concurrent runs cannot collide.
STAGE_ROOT_GLOB="${TMPDIR:-/tmp}/saw-lean-kernel-selftest."

case "$VERB" in
    good) echo "replay-kernel-selftest.sh: 'good' is a no-op"; exit 0 ;;
    clean) rm -rf "$STAGE_ROOT_GLOB"*; exit 0 ;;
    test) ;;
    *) echo "replay-kernel-selftest.sh: unknown verb '$VERB'" >&2; exit 1 ;;
esac

if ! command -v lake >/dev/null 2>&1; then
    echo "FAIL: lake is not on PATH — the trust kernel cannot run" >&2
    exit 1
fi

rm -rf "$STAGE_ROOT"; mkdir -p "$STAGE_ROOT"
trap 'rm -rf "$STAGE_ROOT"' EXIT

status=0
SELFTEST_PINNED=""

# A goal that is real (not rfl/trivial-closable, so it survives the
# anti-trivialization gate) and easy to prove honestly.
real_goal() {
    cat <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
EOF
}
honest_proof() {
    cat <<'EOF'
import Emitted

theorem goal_closed : goal := by
  intro x; cases x <;> rfl
EOF
}

# expect_fail <case> <expected-CHECK-FAIL-name>   (stage prebuilt at $STAGE_ROOT/<case>)
expect_fail() {
    local name="$1" want="$2" out rc
    SELFTEST_PINNED="$SELFTEST_PINNED$want
"
    out=$(bash "$CORE" "$PROJ" "$STAGE_ROOT/$name" 2>&1); rc=$?
    if [ "$rc" -eq 0 ]; then
        echo "FAIL[$name]: kernel ACCEPTED a stage the guard '$want' must reject"
        printf '%s\n' "$out" | tail -4
        status=1
    elif ! printf '%s\n' "$out" | grep -qF "CHECK-FAIL: $want"; then
        echo "FAIL[$name]: rejected, but NOT with 'CHECK-FAIL: $want'"
        printf '%s\n' "$out" | tail -6
        status=1
    else
        echo "OK[$name]: rejected with '$want'"
    fi
}

expect_ok() {
    local name="$1" out rc
    out=$(bash "$CORE" "$PROJ" "$STAGE_ROOT/$name" 2>&1); rc=$?
    if [ "$rc" -ne 0 ] || ! printf '%s\n' "$out" | grep -q '^CHECK-OK'; then
        echo "FAIL[$name]: kernel REJECTED an honest stage (guards must not over-fire)"
        printf '%s\n' "$out" | tail -6
        status=1
    else
        echo "OK[$name]: honest discharge admitted"
    fi
}

mk() { mkdir -p "$STAGE_ROOT/$1"; }

# --- Control: an honest discharge must pass. Without this, every
# rejection below could be produced by a kernel that rejects
# everything, and the whole file would be vacuous.
mk control; real_goal > "$STAGE_ROOT/control/Emitted.lean"
honest_proof > "$STAGE_ROOT/control/proof.lean"
expect_ok control

# Completed-outline ACCEPT control (2026-07-30, from the task-#27 fix
# audit): the kernel's completed path had only REJECT-side coverage
# here — both expect_ok cases were plain-path — so the drift probe's
# accept side (`theorem __drift_binding … := rfl` succeeding on an
# honest outline) was pinned only by the cabal-path workflow rows,
# which exercise the harness's SEPARATE implementation of the gate.
# This case stages an honest completed outline: completed.lean is
# byte-identical to Emitted.lean (as the SAW caller stages it) and
# Generated.lean is the same goal under the GeneratedHarness
# namespace, so every completed-path gate must pass and the run must
# be ADMITTED.
mk completed_ok
real_goal > "$STAGE_ROOT/completed_ok/Emitted.lean"
real_goal > "$STAGE_ROOT/completed_ok/completed.lean"
cat > "$STAGE_ROOT/completed_ok/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
end GeneratedHarness
EOF
honest_proof > "$STAGE_ROOT/completed_ok/proof.lean"
expect_ok completed_ok

# --- replay-emission-missing-goal-def (A-2; the C1 closure).
# A universe-parameterized goal misses the goal-presence regex. Before
# the fix this SILENTLY disabled the binding gate and admitted a proof
# that never mentioned the goal.
mk univgoal
cat > "$STAGE_ROOT/univgoal/Emitted.lean" <<'EOF'
noncomputable def goal.{u0} : Prop :=
  (a : Sort u0) -> (x : Bool) -> @Eq.{1} Bool x (not x)
EOF
cat > "$STAGE_ROOT/univgoal/proof.lean" <<'EOF'
import Emitted

theorem totally_unrelated : 1 + 1 = 2 := rfl
EOF
expect_fail univgoal replay-emission-missing-goal-def

# --- missing-goal_closed: a named closer that is not goal_closed.
mk nocloser; real_goal > "$STAGE_ROOT/nocloser/Emitted.lean"
cat > "$STAGE_ROOT/nocloser/proof.lean" <<'EOF'
import Emitted

theorem some_other_name : goal := by
  intro x; cases x <;> rfl
EOF
expect_fail nocloser missing-goal_closed

# --- closer-wrong-type: THE binding gate (what A-5 defeats).
# goal_closed exists and elaborates, but proves something else.
mk wrongtype; real_goal > "$STAGE_ROOT/wrongtype/Emitted.lean"
cat > "$STAGE_ROOT/wrongtype/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : 1 + 1 = 2 := rfl
EOF
expect_fail wrongtype closer-wrong-type

# --- no-named-closer: only an anonymous `example`.
mk anon; real_goal > "$STAGE_ROOT/anon/Emitted.lean"
cat > "$STAGE_ROOT/anon/proof.lean" <<'EOF'
import Emitted

example : goal := by intro x; cases x <;> rfl
EOF
expect_fail anon no-named-closer

# (trivgoal / trivgoal_deep: retired 2026-07-31 with the
# anti-trivialization gate itself — user decision, design review
# doc/2026-07-31_kernel-design-review.md §3.1 Option B. Their
# subject tokens no longer exist; the residual is documented at
# residual-trust.md §3.2d.)

# --- sorry-in-user-file.
mk usersorry; real_goal > "$STAGE_ROOT/usersorry/Emitted.lean"
cat > "$STAGE_ROOT/usersorry/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : goal := by sorry
EOF
expect_fail usersorry sorry-in-user-file

# --- harness-namespace-in-user-file, KERNEL spelling (the R-1 commit
# pinned only the CI harness's message).
mk nscapture; real_goal > "$STAGE_ROOT/nscapture/Emitted.lean"
cat > "$STAGE_ROOT/nscapture/proof.lean" <<'EOF'
import Emitted

def GeneratedHarness.GeneratedHarness.goal : Prop := True

theorem goal_closed : goal := by
  intro x; cases x <;> rfl
EOF
expect_fail nscapture harness-namespace-in-user-file

# --- A-5: the coercion + hidden-def vector. `goal_closed` is clean
# and trivial; a CoeT instance carries the ascription to `def hidden`,
# which holds the real proof BY NATIVE EVALUATION. `def` is invisible
# to the closer awk (theorem|lemma only), so under the old
# `#check (goal_closed : goal)` probe this printed `hidden : goal` and
# PASSED while the audit inspected only `goal_closed` (clean) —
# putting Lean's COMPILER into the trusted base on a row whose
# evidence record says strict tier.
#
# The kernel-checked binding constant drags the real proof term into
# the audit, so the native axiom is named and rejected. Note the
# guard that fires is the AXIOM ALLOWLIST, not the binding gate: the
# coercion is not itself unsound, and the fix is that its axioms can
# no longer hide (see the acceptance case below).
mk coercion
cat > "$STAGE_ROOT/coercion/Emitted.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := forall (x y : BitVec 8), x * y = y * x
EOF
cat > "$STAGE_ROOT/coercion/proof.lean" <<'EOF'
import Emitted
import Std.Tactic.BVDecide

def hidden : goal := by
  intro x y
  bv_decide

theorem goal_closed : True := trivial

instance : CoeT True goal_closed goal := ⟨hidden⟩
EOF
expect_fail coercion axiom-outside-allowlist

# --- ...and the DELIBERATE non-rejection: the same shape with an
# HONEST proof is admitted. The property the kernel enforces is "a
# kernel-checked term of the goal's type exists and its axioms are
# allowlisted", not "the user wrote it in the expected style". This
# case exists so a future hardening that blanket-bans coercions is
# recognised as a behaviour change rather than a silent tightening.
mk coercion_ok; real_goal > "$STAGE_ROOT/coercion_ok/Emitted.lean"
cat > "$STAGE_ROOT/coercion_ok/proof.lean" <<'EOF'
import Emitted

def hidden : goal := by
  intro x; cases x <;> rfl

theorem goal_closed : True := trivial

instance : CoeT True goal_closed goal := ⟨hidden⟩
EOF
expect_ok coercion_ok

# --- completed-without-generated-reference: a completed outline with
# no authority to drift-check against.
mk noref; real_goal > "$STAGE_ROOT/noref/Emitted.lean"
real_goal > "$STAGE_ROOT/noref/completed.lean"
honest_proof > "$STAGE_ROOT/noref/proof.lean"
expect_fail noref completed-without-generated-reference

# --- completed-outline-drift: the completed goal states something
# ELSE than the authority. This is the gate S-1 shows is blind to an
# erased obligation; pinning it here means a regression that disables
# the gate ENTIRELY still fails loudly, even though the S-1 class
# itself needs the contract fix (see the plan doc §6).
mk drift
cat > "$STAGE_ROOT/drift/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
end GeneratedHarness
EOF
cat > "$STAGE_ROOT/drift/Emitted.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/drift/completed.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/drift/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : goal := by intro x; rfl
EOF
expect_fail drift completed-outline-drift

# --- completed-outline-missing-goal-def (R-1), at the kernel level.
mk r1
cat > "$STAGE_ROOT/r1/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
end GeneratedHarness
EOF
cat > "$STAGE_ROOT/r1/Emitted.lean" <<'EOF'
import CryptolToLean

abbrev goal : Prop := ∀ (x : Bool), x = !(!x)
EOF
cp "$STAGE_ROOT/r1/Emitted.lean" "$STAGE_ROOT/r1/completed.lean"
cat > "$STAGE_ROOT/r1/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : True := trivial
EOF
expect_fail r1 completed-outline-missing-goal-def

# --- B1 (0.02 release-gate audit): NO USER-AUTHORED LEAN IS
# ELABORATED BEFORE THE PURE-TEXT GATES HAVE RUN.
#
# This case exists to pin an ORDERING, which is why the payload
# ERASES ITSELF. A plain `axiom` would be rejected by the source
# lint from either position — before or after the first elaboration —
# so a plain payload says NOTHING about when the lint runs. This one
# is only caught by a lint that runs FIRST. (Retargeted 2026-07-30
# with the D2 lint narrowing: the payload used to be a bare
# self-erasing `run_cmd`, caught because the lint banned `run_cmd`
# itself. The narrowed lint bans only `axiom`, so the payload now
# carries an axiom declaration AND a `run_cmd` eraser that scrubs it
# from every staged copy — the eraser is the vehicle, the axiom is
# the subject. The ordering pin is unchanged in kind:)
#
#   * gates in their pre-fix position: step 1 elaborates
#     Emitted.lean, which on the completed path IS the user's file.
#     The eraser runs, rewrites completed.lean to a clean copy and
#     Generated.lean (the drift AUTHORITY) to agree with the
#     substituted goal, and the lint later reads the clean copy —
#     no axiom found. The staged-digest re-verification then fails
#     the run (`user-file-mutated-mid-check`), so a regression of
#     the ordering surfaces as the WRONG diagnostic here rather
#     than as an admission.
#   * gates in their fixed position: the lint reads the payload
#     before Lean ever runs. Outcome:
#     CHECK-FAIL: axiom-decl-in-user-file.
#
# The payload only touches files under `.replay-stage/`, which is the
# kernel's own per-call working area. It reaches them by enumeration
# because `run_lean` executes with cwd = the project root and the
# stage dir is required to live inside it (lake's constraint, see
# lean-check-core.sh) — that adjacency is the attack surface, not an
# accident of this fixture.
#
# The digest guard (`user-file-mutated-mid-check`) is the second,
# independent line: even a payload the lint does not recognise cannot
# rewrite a staged file without the re-verification firing. It is
# pinned separately below, and the staged-then-DELETED variant
# (`user-file-deleted-mid-check`, K-2's in-model residue) right
# after it.
mk b1elab
cat > "$STAGE_ROOT/b1elab/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
end GeneratedHarness
EOF
b1_payload() {
    cat <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x

axiom b1_smuggled : goal

open Lean Elab Command in
run_cmd do
  let clean := "import CryptolToLean\n\nnoncomputable def goal : Prop := ∀ (x : Bool), x = x\n"
  let auth  := "import CryptolToLean\n\nnamespace GeneratedHarness\nnoncomputable def goal : Prop := ∀ (x : Bool), x = x\nend GeneratedHarness\n"
  let root : System.FilePath := ".replay-stage"
  if (← root.pathExists) then
    for d in (← root.readDir) do
      let c := d.path / "completed.lean"
      let g := d.path / "Generated.lean"
      if (← c.pathExists) then IO.FS.writeFile c clean
      if (← g.pathExists) then IO.FS.writeFile g auth
EOF
}
b1_payload > "$STAGE_ROOT/b1elab/completed.lean"
# The SAW caller stages the completed outline as Emitted.lean too
# (Builtins.hs) — that is precisely what put user bytes in front of
# the elaborator, so the fixture must reproduce it.
b1_payload > "$STAGE_ROOT/b1elab/Emitted.lean"
honest_proof > "$STAGE_ROOT/b1elab/proof.lean"
expect_fail b1elab axiom-decl-in-user-file

# --- proof-source-unlintable (DC-2 exit-code split, 2026-07-30): a
# user file the lint's LEXER rejects — here an unterminated string
# at EOF — must fail closed under a token that says the closed check
# could not run, NOT under `axiom-decl-in-user-file` (the file
# contains no axiom; before the split it was accused of one). This
# also pins the lint's END-block `in_str` guard through the kernel
# (wave-4 DC-3: the two END-block lexer-state checks were the only
# lexer outcomes with no pin after the 17-row retirement).
mk unlintable
real_goal > "$STAGE_ROOT/unlintable/Emitted.lean"
cat > "$STAGE_ROOT/unlintable/proof.lean" <<'EOF'
import Emitted

def s : String := "oops
EOF
expect_fail unlintable proof-source-unlintable

# --- proof-source-unlintable, fatal() half (DC-2 fix-audit F2,
# 2026-07-30): the case above pins only the lint's END-block path;
# five of the seven lexer rejections reach exit 2 through fatal()
# instead, and a one-line mutation there (code = 2 -> 1) reinstated
# the DC-2 mis-token invisibly — every lint_case row is rc-blind
# and stayed green. This case drives a fatal() rejection (raw
# string literal) end-to-end through the kernel and pins its token.
mk unlintable_fatal
real_goal > "$STAGE_ROOT/unlintable_fatal/Emitted.lean"
cat > "$STAGE_ROOT/unlintable_fatal/proof.lean" <<'EOF'
import Emitted

def r1 : String := r"x"
EOF
expect_fail unlintable_fatal proof-source-unlintable

# --- axiom-first precedence (second DC-2 fix audit, F-B,
# 2026-07-30): an axiom on an EARLIER line than a lexer-fatal must
# keep the axiom token — the `if (code == 0)` guard in the lint's
# fatal() is what preserves it, and mutation showed that guard was
# otherwise unpinned (reverting it left every existing fixture
# byte-identical). This file has a real axiom on line 3 and a raw
# string (fatal trigger) on line 5: the lint must exit 1 with the
# axiom line printed, and the kernel must say axiom, not
# unlintable.
mk axiom_then_fatal
real_goal > "$STAGE_ROOT/axiom_then_fatal/Emitted.lean"
cat > "$STAGE_ROOT/axiom_then_fatal/proof.lean" <<'EOF'
import Emitted

axiom smuggled_before_lexer_stop : goal

def r1 : String := r"x"
EOF
expect_fail axiom_then_fatal axiom-decl-in-user-file

# --- user-file-mutated-mid-check: the digest guard on its own, with
# NO test hook in the kernel. A dev-override affordance inside a trust
# path is a residual this project catalogs (residual-trust §3.2c), so
# the guard is exercised through the kernel's ordinary inputs instead.
#
# The lever is that `Generated.lean` is NOT covered by the two text
# gates — they read proof.lean and completed.lean only. That is
# correct in the product, where Generated.lean is the emitter's own
# output and no user controls it; but the selftest DOES control the
# stage, so it can put a metaprogram there and observe what the kernel
# does when a staged file changes underneath it.
#
# Sequence: the drift step re-verifies Generated.lean and
# completed.lean (both still original, so both pass), then compiles
# Generated.lean — at which point the payload rewrites completed.lean.
# The re-verification before the sorry scan then finds the new bytes.
# So this pins that the guard catches a mutation the LINT never saw,
# which is the defence-in-depth half of B1.
mk b1hash
cat > "$STAGE_ROOT/b1hash/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = x
end GeneratedHarness

open Lean Elab Command in
run_cmd do
  let root : System.FilePath := ".replay-stage"
  if (← root.pathExists) then
    for d in (← root.readDir) do
      let c := d.path / "completed.lean"
      if (← c.pathExists) then
        IO.FS.writeFile c "import CryptolToLean\n\nnoncomputable def goal : Prop := ∀ (x : Bool), x = x\n-- rewritten after staging\n"
EOF
cat > "$STAGE_ROOT/b1hash/Emitted.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/b1hash/completed.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/b1hash/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : goal := by intro x; rfl
EOF
expect_fail b1hash user-file-mutated-mid-check

# --- user-file-deleted-mid-check: K-2's in-model residue (D4
# down-scope, 2026-07-30; rule C3). Before the fix,
# `verify_unchanged` opened with `[ -f ] || return 0`, so a staged
# file that VANISHED mid-check read as unchanged — and because the
# completed-vs-plain distinction is re-derived from the filesystem,
# deleting completed.lean silently converted the run to the plain
# path, dropping the drift check while every guard reported success.
# The fix does not latch the path (out-of-model half, dropped);
# it makes absence itself fail at the NEXT verify_unchanged naming
# the file, whichever path the run has taken by then.
#
# Same vehicle as b1hash — a payload in Generated.lean, which no
# text gate scans — but the payload deletes instead of rewriting.
mk b1del
cat > "$STAGE_ROOT/b1del/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = x
end GeneratedHarness

open Lean Elab Command in
run_cmd do
  let root : System.FilePath := ".replay-stage"
  if (← root.pathExists) then
    for d in (← root.readDir) do
      let c := d.path / "completed.lean"
      if (← c.pathExists) then IO.FS.removeFile c
EOF
cat > "$STAGE_ROOT/b1del/Emitted.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/b1del/completed.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/b1del/proof.lean" <<'EOF'
import Emitted

theorem goal_closed : goal := by intro x; rfl
EOF
expect_fail b1del user-file-deleted-mid-check

# --- completed-path-emitted-not-linted (B1's caller-contract assert).
# On the completed path the SAW caller stages the user's outline as
# BOTH completed.lean and Emitted.lean, so linting completed.lean is
# what puts Emitted.lean's bytes behind a gate. That correspondence is
# a property of the CALLER, not of this script, so the kernel asserts
# it rather than assuming it: if a future caller change stages a
# different Emitted.lean, the gate coverage silently shrinks and B1
# reopens. Provoked here by staging the two files with different
# bytes.
mk b1contract
real_goal > "$STAGE_ROOT/b1contract/completed.lean"
cat > "$STAGE_ROOT/b1contract/Emitted.lean" <<'EOF'
import CryptolToLean

noncomputable def goal : Prop := ∀ (x : Bool), x = x
EOF
cat > "$STAGE_ROOT/b1contract/Generated.lean" <<'EOF'
import CryptolToLean

namespace GeneratedHarness
noncomputable def goal : Prop := ∀ (x : Bool), x = !(!x)
end GeneratedHarness
EOF
honest_proof > "$STAGE_ROOT/b1contract/proof.lean"
expect_fail b1contract completed-path-emitted-not-linted

# --- COVERAGE META-GUARD: this is what makes C4 structural rather
# than conventional. Every named `fail "..."` in the trust kernel must
# either be pinned by a case above or appear in the waiver list below
# WITH A REASON. A new guard added without a mutation fails here — so
# the rule cannot rot the way it did before (only 4 of 25 were pinned
# when this was written, including guards whose absence the second
# audit's criticals exploited).
#
# Waivers are for guards that cannot be provoked from a staged input:
# they need a broken environment, not a crafted stage. Each is
# reachable only by breaking the checkout or the toolchain, which is
# threat-model T3 (out of scope — see the plan doc §1).
#
# HARDENED (2026-07-29 convergence work): waivers are a TABLE whose
# rows carry machine-checked evidence, not a bare name list. The bare
# list allowed two rots, both observed in this repo: a waiver whose
# guard no longer exists keeps "covering" nothing (dead waiver), and
# a waiver whose stated reason cites a mechanism that does not exist
# (the 2026-07-29 axiom-outside-allowlist correction — the false
# claim sat inside the very meta-guard whose job is to stop guards
# going unwatched; that guard is now pinned LIVE by the coercion
# case above, and the owed saw-boundary runtime row remains tracked
# in TODO.md's pins-owed section). Row format `guard|evidence`:
#
#   env                  threat-model T3: provoking it means breaking
#                        the checkout/toolchain, not supplying a bad
#                        proof. No evidence beyond the guard existing
#                        (every row gets the dead-waiver check).
#   pinned-sibling:G     a case ABOVE pins guard G, which shares the
#                        failing code path. Checked LIVE against
#                        SELFTEST_PINNED in this run.
#   pin-row:PATH         an end-to-end test row pins it; PATH is
#                        relative to otherTests/saw-core-lean and
#                        must exist.
#   sibling-case:F:PAT   another selftest in support/ exercises it;
#                        PAT must appear in F.
#
# A waiver for a guard already in SELFTEST_PINNED is REDUNDANT and
# fails: if the pinning case were ever deleted, the stale waiver
# would silently reactivate and unwatch the guard.
waivers() {
    grep -Ev '^[[:space:]]*(#|$)' <<'EOF'
# Environment/plumbing: provoking these means breaking the
# installation, not supplying a bad proof. no-digest-guard is the
# exact sibling of no-timeout-guard (B1, 2026-07-29): both are
# non-degradable environment guards, reachable only by removing a
# coreutils binary from the installation. Same T3 rationale.
no-timeout-guard|env
no-digest-guard|env
cannot-create-work-stage|env
# Same family as cannot-create-work-stage: a cp failing mid-staging
# (disk full, permissions) is an environment fault we cannot stage
# portably in a fixture. The guard exists so a failed copy of
# completed.lean cannot silently convert the run to the plain path
# before digests are recorded (task-#26 fix audit, 2026-07-30).
stage-copy-failed|env
project-root-not-absolute|env
stage-dir-not-absolute|env
missing-emitted|env
missing-proof|env
support-library-build|env
# Provoked only by a corrupt/unbuildable AUTHORITY emission, i.e. a
# translator bug, not a user input. Covered on the emitter side by
# the driver rows' elaboration gate.
emitted-does-not-compile|pin-row:drivers
generated-reference-does-not-compile|pin-row:drivers
# Reached only when Lean itself fails to run the audit probe or the
# audit output drifts in format; both are toolchain events. (An
# earlier reason also claimed a pure-awk sibling for -vacuous in
# trust-tier-selftest.sh; making evidence checkable, 2026-07-29,
# showed those awk cases pin the ALLOWLIST semantics, not the
# vacuity count — the claim was decoration and is withdrawn.)
axiom-audit-run|env
axiom-audit-vacuous|env
# (triviality-probe-inconclusive: waiver history retired with the
# gate itself 2026-07-31 — design review §3.1 Option B.)
# axiom-decl-in-user-file needs NO row: the b1elab case above pins
# it live in-kernel (since the 2026-07-29 B1 fix; token renamed with
# the 2026-07-30 D2 lint narrowing), and the saw-boundary rows
# (replay_reject_axiom, _suffix_axiom) pin it end-to-end through SAW
# besides. (replay_reject_notation was retired with the narrowing —
# its subject, the `notation` ban, no longer exists.)
# The waiver that used to sit here was made redundant by b1elab;
# the redundancy check below is what noticed.
#
# The authority is generated by the driver, so a goal-less authority
# means the emitter broke; the completed-path sibling shares the
# code path and is pinned above.
authority-missing-goal-def|pinned-sibling:completed-outline-missing-goal-def
# Emitted-side placeholder policy: provoked by a doctored AUTHORITY,
# not a user file; the user-file half is pinned above.
unsanctioned-sorry-in-emitted|pinned-sibling:sorry-in-user-file
# proof.lean failing to elaborate is pinned implicitly by every case
# above that stages a compiling proof, and explicitly by the negative
# rows, whose harness asserts elaboration failure is loud.
proof-does-not-elaborate|pin-row:negative
EOF
}

kernel_guards=$(grep -oE 'fail "[a-z0-9_-]+"' "$CORE" | sed 's/fail "//;s/"//' | sort -u)
unpinned=0
for g in $kernel_guards; do
    if printf '%s\n' "$SELFTEST_PINNED" | grep -qx "$g"; then continue; fi
    if waivers | grep -q "^$g|"; then continue; fi
    echo "FAIL[coverage]: kernel guard '$g' has no mutation case and no waiver"
    echo "  Add a case to $(basename "$0"), or a waiver row WITH CHECKED EVIDENCE."
    unpinned=$((unpinned + 1))
    status=1
done
if [ "$unpinned" -eq 0 ]; then
    echo "OK[coverage]: every kernel guard is pinned or explicitly waived"
fi

# --- WAIVER-EVIDENCE AUDIT: every waiver row must name a guard that
# still exists, must not duplicate a live pin, and must carry
# evidence that checks out. This is the meta-guard's own meta-guard,
# earned the hard way (see the HARDENED note above).
waiver_bad=0
while IFS='|' read -r wg wev; do
    if ! printf '%s\n' "$kernel_guards" | grep -qx "$wg"; then
        echo "FAIL[waiver]: '$wg' is waived but no such guard exists in the kernel — dead waiver; delete the row"
        waiver_bad=$((waiver_bad + 1)); status=1; continue
    fi
    if printf '%s\n' "$SELFTEST_PINNED" | grep -qx "$wg"; then
        echo "FAIL[waiver]: '$wg' is waived AND pinned by a case — redundant; delete the row"
        waiver_bad=$((waiver_bad + 1)); status=1; continue
    fi
    case "$wev" in
        env) : ;;
        pinned-sibling:*)
            sib="${wev#pinned-sibling:}"
            if ! printf '%s\n' "$SELFTEST_PINNED" | grep -qx "$sib"; then
                echo "FAIL[waiver]: '$wg' cites pinned sibling '$sib', which no case in this run pinned"
                waiver_bad=$((waiver_bad + 1)); status=1
            fi ;;
        pin-row:*)
            row="${wev#pin-row:}"
            if [ ! -e "$HERE/../$row" ]; then
                echo "FAIL[waiver]: '$wg' cites test row '$row', which does not exist"
                waiver_bad=$((waiver_bad + 1)); status=1
            fi ;;
        sibling-case:*)
            spec="${wev#sibling-case:}"
            sfile="${spec%%:*}"
            spat="${spec#*:}"
            if ! grep -q "$spat" "$HERE/$sfile" 2>/dev/null; then
                echo "FAIL[waiver]: '$wg' cites '$spat' in support/$sfile, which does not match"
                waiver_bad=$((waiver_bad + 1)); status=1
            fi ;;
        *)
            echo "FAIL[waiver]: '$wg' has unknown evidence kind '$wev'"
            waiver_bad=$((waiver_bad + 1)); status=1 ;;
    esac
done < <(waivers)
if [ "$waiver_bad" -eq 0 ]; then
    echo "OK[waiver-audit]: every waiver names a live guard and checkable evidence"
fi

if [ "$status" -eq 0 ]; then
    echo "replay-kernel-selftest: ALL CASES OK"
fi
exit $status
