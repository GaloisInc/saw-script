# Internal investigation: root-cause the 101 P4-WIP errors

*Agent report — 2026-04-22*

This complements `2026-04-22_universe-external-research.md` with the
concrete per-error analysis of the P4-WIP output. Headline: the
~100 errors are three related variants of *one* translator bug; the
fix is small and validated.

## The bug in one sentence

`translateSort` names universe variables by SAWCore sort level
(`u0`, `u1`), so every `sort 1` occurrence in a def shares the
same Lean universe variable. This forces the variable to satisfy
*all* of the def's `sort 1` constraints simultaneously — which is
impossible when one occurrence is a binder's type (`t : sort 1`,
needing a concrete type) and another is a motive's return type
(`(p : ... → sort 1)`, needing to accept `Prop`).

## Error taxonomy (101 errors, all type-mismatch)

| Group | Count | Defs affected | Root mechanism |
|---|---|---|---|
| A | ~60 | `eq_cong`, `sym`, `trans`, `inverse_eta_rule`, `coerce_same`, `piCong0`, `piCong1` | `Eq__rec` monomorphic in one `u1`; motive returning `Prop` conflicts with binder type |
| B | ~15 | `coerce__def`, `coerce_same`, `coerce__def_trans`, `coerce_trans` | Same `Eq__rec` issue with `t := Type` as a value |
| C | ~25 | `ite_true`, `ite_false`, `ite_nest{1,2}`, `ite_not`, plus ~20 Bool theorems | The handwritten `ite`/`iteDep` in `SAWCorePreludeExtra.lean` is monomorphic at `Type`; callers pass `Sort u` |

All three share the underlying issue.

## Traces

### `eq_cong` (line 98)
- SAWCore: `(t : sort 1) → (x y : t) → Eq t x y → (u : sort 1) → (f : t → u) → Eq u (f x) (f y)`
- P4-WIP emits: `eq_cong.{u1} (t : Sort u1) (x y : t) ... (u : Sort u1) (f : t → u) ...`
- **Bug:** two binder occurrences of `sort 1` share `u1`. But they should be independent — a caller might pass `t := Bool` and `u := Prop`.
- At the call to `Eq__rec ...`, the motive returns `Prop` = `Sort 0`, forcing `u1 := 0`, which in turn forces `t : Prop`. Unification refuses.
- **Fix:** emit `eq_cong.{u1, u2}` with `t : Sort u1, u : Sort u2`. Then the `Eq__rec.{u1, u2}` used inside takes them independently.

### `coerce__def` (line 202)
- SAWCore: `(a b : sort 0) → Eq (sort 0) a b → a → b`
- P4-WIP emits: `coerce__def (a b : Type) (eq : @Eq Type a b) (x : a) : b := Eq__rec Type a (fun b' _ => b') x b eq`
- `coerce__def` itself needs no universe variables (only `sort 0` at binders). But its body calls `Eq__rec`, and `Eq__rec.{u1}`'s single `u1` can't simultaneously be `2` (for `t := Type`) and `1` (for motive returning `b' : Type`).
- **Fix:** make `Eq__rec` two-universe as above, and Lean picks `.{2, 1}` at this call site automatically.

### `uip` (line 95)
- Elaborates fine. Has one `sort 1` binder, no internal `Eq__rec` call, so one `u1` is enough.

## Probe validation

The agent wrote 7 probe files under `.tmp/probes/` (gitignored) that
exercise the fixed shape of `Eq__rec`, `eq_cong`, `coerce__def`, and
the `ite`/`iteDep` support lib. All probes elaborate cleanly. The
fix is demonstrable.

## What to change in the translator

### Change 1: `SAWCoreLean.Term.translateSort`

Current (wrong): deduplicates universe variables by sort level.

```haskell
translateSort s
  | s == propSort = pure Lean.Prop
  | otherwise = case s of
      TypeSort 0 -> pure Lean.Type
      TypeSort n -> do
        let uname = "u" ++ show (fromIntegral n :: Integer)
        modify (over universeVars (Set.insert uname))
        pure (Lean.SortVar uname)
```

Fix: each invocation allocates a fresh variable name (and the
variable set grows accordingly).

```haskell
translateSort s
  | s == propSort = pure Lean.Prop
  | otherwise = case s of
      TypeSort 0 -> pure Lean.Type
      TypeSort _ -> do
        -- Per-call fresh universe variable. Sharing by sort level
        -- incorrectly conflates independent binder occurrences
        -- (e.g. Eq__rec's `t : sort 1` and its motive's return
        -- `sort 1` need independent Lean universe variables).
        current <- view universeVars <$> get
        let uname = freshUniverse current
        modify (over universeVars (Set.insert uname))
        pure (Lean.SortVar uname)
  where
    freshUniverse used =
      head [ "u" ++ show (n :: Int)
           | n <- [1..]
           , ("u" ++ show n) `Set.notMember` used
           ]
```

Only `sort k ≥ 1` at binder positions triggers fresh allocation.
`sort 0` stays as concrete `Lean.Type`. Value-level `Sort` nodes
(which only appear as arguments, e.g. `Eq (sort 0) a b`) also stay
concrete by the same logic — we're inside `translateFTermF`'s
`Sort` case, and the caller determines context.

Wait — actually `translateSort` is called both at binder positions
(via `translatePiBinder` / `translateBinder`) and at value
positions (via `translateFTermF`'s `Sort` case). We need to
distinguish: binder positions get fresh variables; value positions
emit `Type k` with concrete level.

Easiest implementation: `translateSort` gets two variants, and
callers pick the right one.

### Change 2: SAWCorePreludeExtra.lean → universe-polymorphic support

```lean
-- Current (monomorphic):
@[reducible] noncomputable def iteDep (p : Bool → Type) (b : Bool) (fT : p true) (fF : p false) : p b
  := Bool.rec fF fT b

-- Fixed (universe-polymorphic):
@[reducible] noncomputable def iteDep.{u} (p : Bool → Sort u) (b : Bool)
    (fT : p true) (fF : p false) : p b :=
  Bool.rec fF fT b
```

Same for `ite`, `iteDep_True`, `iteDep_False`, `ite_eq_iteDep`.
All `rfl` proofs stay valid since `Bool.rec` is universe-polymorphic.

## Risks / corner cases

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| 1 | Universe list bloat (`.{u1, u2, u3, ...}` per def) | high | cosmetic only; can dedupe within a binder path later |
| 2 | Lean's universe inference picks wrong instantiation | medium | fall back to explicit `.{u, 0}` via Option D2 per call |
| 3 | Inductive result `max 1 (u1 ∪ u2 ∪ ...)` logic wrong | low-medium | audit multi-param inductives explicitly |
| 4 | Per-binder freshness breaks inductive ctor types | low | constructors reference bound variables, not sort nodes |
| 5 | Bool constructor-order landmine | unrelated | P2 already fixed; no regression |

## Effort estimate

1–2 days, mostly:
- 30min: translateSort rewrite
- 30min: audit universeVars collection
- 1h: universe-polymorphic SAWCorePreludeExtra
- 2–4h: end-to-end validation + iteration
- 2–4h: regression tests

## Confidence

- **High**: the three groups cover 101/101 errors. All probed.
- **High**: Option D1 (per-binder fresh) handles all three groups.
- **Medium**: per-binder-freshness handles arbitrary SAWCore. Reasoning from
  first principles; the rule is intuitively simple but not
  exhaustively proven for pathological cases (nested polymorphic
  sharing, recursive types with universe-polymorphic ctors).

## Where the fix lives

- `saw-core-lean/src/SAWCoreLean/Term.hs`: `translateSort` and
  its callers.
- `saw-core-lean/lean/CryptolToLean/SAWCorePreludeExtra.lean`:
  universe-polymorphic `ite`/`iteDep` family.
- Optional: `saw-core-lean/src/SAWCoreLean/SAWModule.hs`: audit
  the inductive `SortMax1Var` logic for multi-universe cases.

Infrastructure already in place from P4-WIP:
- `Language.Lean.AST.Sort.SortVar`, `SortMax1Var`
- Universe lists on `Definition`, `Axiom`, `Inductive`
- Pretty-printer `.{u v}` emission
- `TranslationState.universeVars` collection
