# K-1 prep: measured basis for inverting the proof-side lint to an allowlist

Read-only measurement taken 2026-07-30 while the suite/audit held the
editable files. Feeds task #19.

## Method note (the first attempt was wrong)

A naive `grep -oE "^[a-z_]+"` over `proof.lean` returned ~120 "heads"
including `the`, `standalone`, `discharge`, `and` — prose inside
`/- … -/` block comments. `proof-source-lint.awk` strips comments
before matching, so the naive count is not what the lint sees.
Re-measured with block- and line-comment stripping, counting only
tokens at column 0 (top-level commands).

## Result: 7 legitimate heads, across 77 `proof.lean` files

| head | uses | role |
|---|---|---|
| `theorem` | 226 | the discharge itself |
| `import` | 99 | preamble |
| `open` | 86 | preamble |
| `noncomputable` | 17 | modifier prefix (`noncomputable def`) |
| `end` | 16 | closes `namespace`/`section` |
| `def` | 8 | helper definitions |
| `abbrev` | 6 | helper abbreviations |

## The three banned-head occurrences are all negative rows

`axiom` (2) and `notation` (1) DO appear at column 0 — and every one is
a row whose purpose is to be rejected:

- `saw-boundary/replay_reject_axiom/rejected_proof/proof.lean` →
  `axiom unsound_axiom : goal`
- `saw-boundary/replay_reject_suffix_axiom/rejected_proof/proof.lean` →
  `axiom unsound_vecToBitVec_bitVecToVec : goal`
- `saw-boundary/replay_reject_notation/rejected_proof/proof.lean` →
  `notation "goal" => True`

So an allowlist of the 7 heads above costs **zero** on legitimate
files and still rejects all three existing negative probes — the same
"measured cost when added: ZERO" standard the lint file already sets
for its denylist.

## Design caveat — measurement is necessary but NOT sufficient

The corpus uses only 7 heads, but a *user* proof may legitimately use
vocabulary the corpus happens not to: `lemma`, `example`, `section`,
`namespace`, `variable`, `instance`, `structure`, `private`,
`@[simp]`-style attributes on a theorem, `local notation`. An allowlist
derived purely from the corpus would refuse those and be a worse
regression than the hole it closes — this is the same trap as gate 3's
first two cuts, where a corpus cost of zero hid a real user-facing
over-refusal.

So the allowlist must be chosen by JUDGEMENT about what a proof file
legitimately contains, with the corpus as a floor rather than the
definition. Proposed set, to be reviewed before implementing:

- discharge/decl: `theorem`, `lemma`, `example`, `def`, `abbrev`,
  `instance`, `structure`, `inductive`?
- modifiers: `noncomputable`, `private`, `protected`, `partial`?
- scoping: `import`, `open`, `section`, `namespace`, `end`, `variable`,
  `universe`
- deliberately EXCLUDED (the point of the exercise): `axiom`, `macro*`,
  `elab*`, `simproc*`, `run_*`, `initialize`, `attribute`, `notation`,
  `syntax`, `infix*`, `prefix`, `postfix`, `declare_syntax_cat`,
  `binder_predicate`, `unif_hint`, `export`, `set_option`, `#eval`,
  `deriving`?
- open question: attribute syntax `@[...]` before a theorem, and
  `local`/`scoped` prefixes — these are not simple heads and need a
  tokenizer rule, not a word match.

The residual risk of an allowlist is the mirror of the denylist's: a
denylist fails OPEN on a new Lean command, an allowlist fails CLOSED
on a legitimate one. Failing closed is the right direction for a
trust-kernel gate, but it must be paired with a clear diagnostic that
tells the user which head was refused and how to request it.
