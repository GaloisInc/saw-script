#!/usr/bin/env python3
"""LIB-1 corpus census — the checked-in form of the measurement the
shipped scope claim rests on.

F5 (0.02 release-gate audit, 2026-07-29). The 59/350 figure in
`doc/2026-07-28_lib1-scope-measurement.md`, README.md and
residual-trust §3.2e was produced by a one-off scratch script. A user
bounds their exposure to the one shipped soundness defect by that
number, and a number nobody re-derives drifts silently as the corpus
grows. This script makes it a RE-DERIVED fact, run by test.sh.

It answers two questions, and asserts both:

  1. How many emitted artifacts carry a THROWING helper inside an
     ELEMENT POSITION of a COLLAPSING helper? (the 59)
  2. How many carry a throwing let-RHS bound OUTSIDE an element span
     and referenced INSIDE it? (the reference-closure escape count,
     retracted to 0 on 2026-07-29 and asserted here so the retraction
     is re-derived rather than re-asserted)

WHAT THIS MEASURES, PRECISELY. LIB-1 is the collapse of an erring
element by the `Except String (Vec n T)` carrier, where SAW's
element-lazy vectors would never force that slot. So the hazard needs
a thrower reachable per-element AND a slot SAW does not force. This
census measures the first conjunct only; it is an upper bound on the
hazard, and deliberately so — a gate must not admit on the strength of
"probably unobserved".

KNOWN BLIND SPOT, found 2026-07-29 while building this pin, by the
row that exposed it (drivers/foldl_under_applied_partial). The element
scan recognises an element position spelled as a LAMBDA — `(fun … )`
— because that is how the emitter writes `gen`/`fold` element
functions today. It does NOT recognise a bare partially-applied name
in the same slot, e.g. `foldlM … (bvUDiv_runtimeM 16) …`, which the
under-applied partial-op path emits. That shape is currently NOT a
LIB-1 hazard for a different reason (a left fold forces every element
on both sides, so there is no unforced-slot divergence), which is why
the count below is unchanged by it — but the two facts are
independent, and a future collapsing helper that IS lazy in a
bare-name element argument would be missed. Recorded rather than
silently patched: widening the scan would change the published number
for a reason unrelated to the hazard, and the honest fix belongs with
the (a) carrier work that removes the hazard class entirely.
"""

import os
import re
import subprocess
import sys

THROWERS = [
    "saw_throw_error", "atRuntimeCheckedM",
    "divNat_runtimeM", "modNat_runtimeM", "divModNat_runtimeM",
    "intDiv_runtimeM", "intMod_runtimeM",
    "bvUDiv_runtimeM", "bvURem_runtimeM", "bvSDiv_runtimeM",
    "bvSRem_runtimeM", "ecSDiv_runtimeM", "ecSMod_runtimeM",
    "ratio_runtimeM", "rationalRecip_runtimeM",
]
THR_RE = re.compile(r"\b(" + "|".join(THROWERS) + r")\b")

# Helpers whose carrier collapses an erring element into failure of
# the whole structure.
GEN_FOLD = re.compile(r"\b(genWithBoundsM|genM|foldrM|foldlM)\b")
VEC_SEQ = re.compile(r"\bvecSequenceM\b")

LET_BIND = re.compile(r"\blet\s+(x__[A-Za-z0-9_']*)\s*:=")

# Expected facts. A change in either is a LOUD failure, not a silent
# re-baseline: the shipped documents quote these.
EXPECT_IN_ELEMENT = 59
EXPECT_REF_ESCAPES = 0

# The corpus SIZE is asserted too, and that is not bookkeeping. The
# harness deletes stale artifacts and re-emits on every run, so a
# census run against a partial corpus reports a LOWER exposure number
# — the dangerous direction, and silently. Found the hard way
# 2026-07-29: scanning mid-run gave 27/324 instead of 59/353 and
# looked like good news. Run this only after a complete emission
# (test.sh invokes it last).
EXPECT_SCANNED = 354


def strip_line_comments(src):
    out = []
    for line in src.split("\n"):
        out.append("" if line.lstrip().startswith("--") else line)
    return "\n".join(out)


def balanced(src, i, op, cl):
    """i indexes op; return exclusive end index of the matching close."""
    depth = 0
    j = i
    n = len(src)
    while j < n:
        c = src[j]
        if c == op:
            depth += 1
        elif c == cl:
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return n


def element_spans(src):
    """[(helper, span_text, (start, end))] for each element position."""
    res = []
    for m in GEN_FOLD.finditer(src):
        j = m.end()
        n = len(src)
        while j < n:
            c = src[j]
            if c == "(":
                if re.match(r"\(\s*fun\b", src[j:j + 8]):
                    e = balanced(src, j, "(", ")")
                    res.append((m.group(1), src[j:e], (j, e)))
                    j = e
                    continue
                j = balanced(src, j, "(", ")")
                continue
            if c in ");":
                break
            j += 1
    for m in VEC_SEQ.finditer(src):
        j = src.find("#v[", m.end())
        if j != -1 and j - m.end() < 400:
            e = balanced(src, j + 2, "[", "]")
            res.append(("vecSequenceM", src[j:e], (j, e)))
    return res


def reference_closure_escapes(src, spans):
    """Throwing let-RHS bound OUTSIDE an element span, referenced INSIDE.

    This is the property a rejection gate must have (see the design
    note): a span-local scan is blind to it. Asserted at 0 so the
    2026-07-29 retraction stays re-derived.
    """
    escapes = []
    for m in LET_BIND.finditer(src):
        name = m.group(1)
        rhs_start = m.end()
        rhs_end = src.find(";", rhs_start)
        if rhs_end == -1:
            rhs_end = len(src)
        rhs = src[rhs_start:rhs_end]
        if not THR_RE.search(rhs):
            continue
        bound_inside_some_span = any(s <= m.start() < e for _, _, (s, e) in spans)
        if bound_inside_some_span:
            continue
        ref = re.compile(r"\b" + re.escape(name) + r"\b")
        for helper, span, _ in spans:
            if ref.search(span):
                escapes.append((name, helper))
                break
    return escapes


def emitted_files(root):
    """The EMITTED corpus, defined exactly as the snapshot oracle does
    (support/emitted-lean-snapshot.sh): every `*.lean` git does NOT
    track. Goldens, hand-written observers, proof scripts and shape
    probes are tracked SOURCES, not emitter output — counting them
    would inflate the published figure with files the emitter never
    produced. Sharing the definition with the oracle is deliberate:
    two mechanisms disagreeing about what "emitted" means is exactly
    how a census drifts from the corpus it claims to describe.
    """
    tracked = set(subprocess.run(
        ["git", "ls-files", "*.lean"], cwd=root, check=True,
        capture_output=True, text=True).stdout.split())
    out = []
    for dirpath, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs
                   if d not in (".snapshots", ".lake", ".elan", ".git")]
        for f in files:
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, f), root)
            if rel not in tracked:
                out.append(rel)
    return sorted(out)


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..")
    in_element = {}
    escapes = {}
    scanned = 0
    for rel in emitted_files(root):
            path = os.path.join(root, rel)
            src = strip_line_comments(open(path, encoding="utf-8").read())
            scanned += 1
            spans = element_spans(src)
            hit = set()
            for _helper, span, _pos in spans:
                hit.update(THR_RE.findall(span))
            if hit:
                in_element[rel] = sorted(hit)
            esc = reference_closure_escapes(src, spans)
            if esc:
                escapes[rel] = esc

    print(f"lib1-census: scanned {scanned} emitted .lean file(s)")
    print(f"lib1-census: in-element throwers   = {len(in_element)} "
          f"(expected {EXPECT_IN_ELEMENT})")
    print(f"lib1-census: ref-closure escapes   = {len(escapes)} "
          f"(expected {EXPECT_REF_ESCAPES})")

    status = 0
    if scanned != EXPECT_SCANNED:
        status = 1
        print(f"lib1-census: FAIL — scanned {scanned} artifacts, expected "
              f"{EXPECT_SCANNED}.")
        print("  A PARTIAL corpus under-reports the figure below, which is the")
        print("  direction that understates a user's exposure. If rows were")
        print("  added or removed deliberately, update EXPECT_SCANNED in the")
        print("  same commit; if not, this ran against an incomplete emission")
        print("  (mid-sweep, or before `make test` finished).")
    if len(in_element) != EXPECT_IN_ELEMENT:
        status = 1
        print("lib1-census: FAIL — the in-element thrower count moved.")
        print("  This number is quoted in README.md, residual-trust §3.2e and")
        print("  doc/2026-07-28_lib1-scope-measurement.md as the bound a user")
        print("  uses to size their exposure to LIB-1. Update all three, or")
        print("  explain why the corpus changed, before adjusting EXPECT_*.")
        for rel in sorted(in_element):
            print("   ", rel, in_element[rel])
    if len(escapes) != EXPECT_REF_ESCAPES:
        status = 1
        print("lib1-census: FAIL — a reference-closure escape appeared.")
        print("  A throwing let-RHS bound outside an element span and")
        print("  referenced inside it means the published figure is no longer")
        print("  EXACT for this corpus, and any span-local gate is blind to")
        print("  the difference.")
        for rel, e in sorted(escapes.items()):
            print("   ", rel, e)
    if status == 0:
        print("lib1-census: OK — both figures re-derived, not re-asserted")
    return status


if __name__ == "__main__":
    sys.exit(main())
