# Stage 1: dependency analysis for implRev4

*Draft — 2026-04-23*

Stage 1 of the specialization-approach de-risking in
`2026-04-23_specialization-approach.md`. Answers the question:
"for the saw-lean-example driving instance, how many SAWCore
constants does the fully-specialized term transitively reference,
and are they all easy translation targets?"

## Method

Used SAWScript's `normalize_term` (requires
`enable_experimental`) on `{{ implRev\`{4, [8]} }}`. The output is
the fully beta/delta-reduced SAWCore term, with Cryptol-prelude
wrappers unfolded into SAWCore-prelude primitives.

Reproduction:

```bash
cd /Users/miked/Projects/claude-lean-saw/saw-lean-example
/path/to/saw depanalysis.saw
```

The driving script is committed at
`saw-lean-example/depanalysis.saw`.

## Result

Normalized `implRev4` is ~35 lines of SAWCore. It references
**exactly these primitives**:

### Types / datatypes
- `Vec n a` (Prelude primitive)
- `Bool`, `Nat` (Prelude inductives)
- `Either a b` (Prelude inductive)
- `Num` (Cryptol inductive), `TCNum` (constructor)
- `Stream` (Prelude; referenced but never reached under normalize
  since `Num#rec1`'s TCInf branch is dead)
- `Integer` (opaque)

### Constructors
- `Left`, `Right` (Either)
- `Refl` (Eq)

### Eliminators / recursors
- `Eq#rec1` (auto-generated)
- `Num#rec1` (auto-generated)
- `Either#rec` (auto-generated)

### Prelude axioms / primitives
- `coerce` (primitive)
- `unsafeAssert` (axiom)
- `error` (axiom)

### Arithmetic
- `subNat`, `addNat` (Prelude primitives)
- `intSub`, `intNeg`, `natToInt`, `intToNat`, `intLe` (Prelude
  primitives)

### Vector operations
- `gen` (Prelude primitive)
- `atWithDefault` (Prelude primitive)

### Branching
- `ite` (Prelude def)

**Total: about 22 distinct names.** Compare to the full SAWCore
Prelude's ~300 named defs + the Cryptol prelude's ~200 wrappers.
Specialization pulls in roughly 5% of what the whole-prelude
approach emits.

## Implications for specialization feasibility

### Positive

- Every primitive above is either a SAWCore axiom (translates
  trivially to a Lean `axiom`) or a SAWCore inductive + its
  auto-generated recursor (translates to a Lean `inductive` + uses
  of `Foo.rec`). The translator already handles both cases in the
  current P2 code.

- `Num`, `TCNum` as translated under specialization becomes simply
  `Num` (the Cryptol-side inductive from `Cryptol.sawcore`) and
  `TCNum` (its constructor). No `seq`, no `ecAt`, no arithmetic
  wrappers — all already reduced.

- There's one `sort 0` in the normalized term
  (`Num#rec1 (\\(num : Num) -> sort 0) ...`) but it's in a motive
  position that's locally concrete (the result sort of the `Num#rec1`
  motive is a `sort 0`). Should translate to `Lean.Type` without
  universe-polymorphism drama.

### Concerns

- **Let-bindings** (`x\`1 = ... ; ... in ...`) need to translate to
  Lean's `let`. The translator already supports `Lean.Let`; the
  Phase-1 shared-subterm lifting walk does this. Confirm it works
  end-to-end on normalized output.

- **The Eq#rec1 occurrence has `sort 0` twice**: `Eq#rec1 Num x\`5
  (\(y' : Num) -> \(eq' : Eq Num x\`5 y') -> Eq sort 0 x\`8 ...)
  (Refl sort 0 x\`8) x\`3 (unsafeAssert Num x\`5 x\`3)`. The inner
  `Eq sort 0 x\`8 ...` is an `Eq` at `sort 0` — i.e. an equality
  between two types. In Lean, `Eq (Type) a b` where `a, b : Type`
  is fine (concrete universe). Should work.

- **`error Integer "..."`** is `error` (an axiom) applied to a type
  and a string literal. The translator handles `StringLit`.

- **Inductives like `Num`, `Either`, `Nat`** appear both as types
  and via their recursors. The translator's `Recursor` case emits
  `@Foo.rec`; no issue.

### What specialized output would look like

A sketch of the target Lean output for `implRev4` (not
syntactically exact, but illustrative):

```lean
/- imports -/
import CryptolToLean

noncomputable def implRev4 : Vec 4 (Vec 8 Bool) → Vec 4 (Vec 8 Bool) :=
  fun (xs : Vec 4 (Vec 8 Bool)) =>
    let x1 := Vec 8 Bool;
    let x4 := subNat 4 0;
    let x5 := TCNum x4;
    let x6 := Vec 4 x1;
    let x7 := error x1 "at: index out of bounds";
    let x8 := Vec x4 x1;
    coerce x8 x6
      (@Eq.rec1 Num x5
        (fun (y' : Num) (eq' : @Eq Num x5 y') =>
          @Eq Type x8
            (@Num.rec1 (fun _ => Type)
              (fun (n : Nat) => Vec n x1)
              (Stream x1) y'))
        (@Eq.refl Type x8)
        (TCNum 4)
        (unsafeAssert Num x5 (TCNum 4)))
      (gen x4 x1 (fun (i : Nat) => ...))
```

Universe resolution is trivial because:
- Every `sort 0` in the normalized term is a concrete `Type`.
- No universe variables appear.
- No `max` expressions.

## Risks identified

1. **`Num#rec1` and `Either#rec` handling.** SAWCore's auto-generated
   recursors need to translate to Lean's auto-generated `.rec`. Our
   translator does this, but we should probe whether a concrete
   specialized call elaborates cleanly. (Concrete concern: the
   motive `fun (num : Num) -> sort 0` passes `sort 0` as a value —
   i.e. passes `Type` as a value-level argument to the motive's
   return-position in the universe hierarchy. Probe needed.)

2. **`Eq#rec1` with `sort 0` motive return.** Lean's core `Eq.rec`
   accepts a motive at any sort. At concrete `Type 0` this should
   work, but worth a probe.

3. **`subNat 4 0` is a primitive, not a def.** SAWCore treats it
   as a `primitive` (axiom). The translator emits it as
   `@SAWCorePrelude.subNat 4 0`. Lean sees an uncomputed axiom
   applied to args — should typecheck at `Nat` even though it's
   opaque.

4. **`error` at a variable type.** `error x\`1 "index out of
   bounds"` where `x\`1 := Vec 8 Bool`. The axiom `error : (a :
   sort 0) -> String -> a`. Translated as polymorphic axiom, called
   at `Vec 8 Bool`. Concrete, should work.

## Unknowns addressed

| Unknown | Status |
|---|---|
| Q1 (blocker): does SAWCore expose a beta-reduce primitive? | Yes — `normalize_term`, `beta_reduce_term`, plus delta-reducing via `unfold_term`. These are SAWScript-level, but the underlying `scReduceTerm` in SAWCore (call it directly in translator) is the right tool. |
| Q2 (blocker): does specialization terminate on Prelude defs? | Yes for `implRev4`. `normalize_term` produced ~35 lines, no infinite unfolding. |
| Q3 (blocker): does hand-specialization elaborate in Lean? | Stage 2 — next step. |
| Q4-Q5 (scale): how big is the output? | Small. 22 distinct names for `implRev4`. Even 10x growth for a bigger spec keeps us well under 500 total. |

## Next: Stage 2

Take the normalized SAWCore term above, construct by hand a Lean
file that represents it directly (with all referenced SAWCore
primitives as handwritten axioms / inductives), and verify it
elaborates under `lake env lean`.

If Stage 2 succeeds, we have high confidence and can proceed to
translator implementation. If it fails, we learn why before
committing engineering time.

## One observation for the planning note

The planning note assumed we'd "beta-reduce the body at SAWCore
level" in `translateConstant`. This is correct, but it's worth
noting that what we actually want is `normalize_term` semantics —
unfold *every* defined constant in a call chain, not just
single-step beta. The SAWCore machinery for this exists
(`scTypeOf`, `scDefUnfolder`, shared-term reduction).
