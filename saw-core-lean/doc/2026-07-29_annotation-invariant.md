# The annotation invariant (2026-07-29)

The Family-3 design note. Family 3 is the defect family named in
`doc/2026-07-28_defect-families-and-sequencing.md` — EMISSION
CONVENTIONS (F-8, F-1, A-4, F-6/F-7, F-2 core) — and it was the one
family with no stated root, which is why its fixes read as
whack-a-mole: nothing said what would make them stop.

This note states the invariant, names where its chokepoint lives,
and is honest about the part of the surface the chokepoint does not
yet cover. It is written against the module structure landed in the
same pass (the `Term.hs` split), because the previous structure had
nowhere to state it: the surface was a property distributed over a
5,647-line file.

## The invariant

> **The emitted signature must derive from the same authority as the
> emitted body.**

Concretely, for every emitted Lean declaration:

- the body is produced by the translator at some *position*, and the
  translator records what representation it actually produced (the
  `TranslatedTerm`'s `BindingShape`);
- the type ANNOTATION is produced by a second, independent path —
  translating the SAWCore type — and then adjusted;
- the invariant demands that the adjustment be computed FROM the
  body's recorded production, not from a re-derivation of what the
  body "should" have been.

Violating it is not automatically unsound. Every violation found so
far is LOUD: Lean rejects the artifact, because a signature that
disagrees with its body is exactly what a type checker catches. The
reason the invariant matters anyway is the charter's: a boundary
whose failure mode is "Lean happens to notice" is a boundary we have
not argued, and F-1 (below) is a shipped path with no compiling
witness precisely because nobody was required to argue it.

## Why this is the root of Family 3

The position/callee calculus (`doc/2026-07-02_position-callee-calculus.md`)
made *adaptation* safe. Every representation change goes through one
chokepoint, `adaptTo`, and the forbidden adaptations are
unrepresentable there rather than merely unreached. That is the
by-construction discipline this project prefers, and it works: the
adaptation half of the emitter has produced no defect of this class.

It left *annotation* unguarded. There is no `adaptTo` for "what type
does this declaration claim", so each top-level emitter answered the
question for itself. The 2026-07-18 exception hunt found the
predictable consequence — three emitters had hand-copied the answer
and one copy had already drifted — and introduced
`topLevelDefConvention` as the single authority. That fixed the
DUPLICATION. It did not supply the invariant, because the authority
it consolidated is still expressed over a vocabulary too coarse to
carry it.

## The vocabulary gap

`BindingShape` (Convention.hs) has three constructors:

    BindingRaw | BindingWrapped | BindingFunction

`BindingRaw` and `BindingWrapped` are precise: they say exactly
whether the produced term sits at the `Except String _` level.
`BindingFunction` says only "this is a function". It records
**nothing about the representation of the function's formals or
result**, and that omission IS F-1:

- `lowerPartialOpRuntimeWrapper` lowers an under-applied partial op
  (a dictionary field like `div = intDiv`) to a support-library
  runtime wrapper, e.g. `divNat_runtimeM`, whose Lean type is
  `Except String Nat -> Except String Nat`.
- It returns `TranslatedTerm app BindingFunction`.
- At top level, `topLevelDefConvention` asks `shouldWrapBinder tp`
  of the SAWCore type `Nat -> Nat`. A Pi type does not wrap, and the
  body's shape is `BindingFunction`, not `BindingWrapped` — so the
  annotation is emitted RAW.
- The emitted declaration is
  `noncomputable def … : Nat -> Nat := divNat_runtimeM …` — a raw
  arrow annotating a wrapped-arrow body. Ill-typed.

The body's authority (a wrapped-arrow function) and the signature's
authority (the SAWCore Pi, translated raw) disagree, and the
vocabulary connecting them cannot express the disagreement. That is
the invariant violated, stated in one sentence — and note that it is
a *representation* defect, not an arity or naming one, which is why
F-6/F-7's naming work and F-8's structural work did not reach it.

## Where the chokepoint lives

`SAWCoreLean.Signature` — extracted from `SAWCoreLean.Term` in this
pass — is the named home. It holds:

- `topLevelDefConvention`: the single authority for the two questions
  every top-level emitter must answer identically (the position the
  body stands at, and whether the annotation wraps). All three
  top-level emitters (`translateDefDocWithArity`, CryptolModule,
  SAWModule) call it.
- `mkDefinitionWith`: the constructor that actually assembles the
  emitted declaration from a name, universes, a body and a type.
  Note that it is reachable from BOTH the top-level path and, via
  `emitImportedRealizationAlias`, from inside the translator knot —
  the two-path structure the invariant is about, visible as an import
  edge.
- The telescope fingerprint (`sawBinderFp` / `leanBinderFp` /
  `telescopeFpMismatch`): the one place today that CHECKS a declared
  signature against the SAWCore type it claims to express. It is a
  partial check by design — coarse type-family fingerprints, with
  `FpOther` a wildcard on either side — and it can only REFUSE, never
  admit. It is a check, not the invariant: it compares the SAW type
  to the emitted Pi spine, not the body's recorded production to the
  annotation.

Placing these in one module below the translator, with the layering
enforced by the compiler (`Convention` → `Calculus` → `Signature` →
`Obligations` → `Term`, zero upward edges), is what makes "the
annotation surface" a thing a reviewer can read rather than a
property to be reconstructed.

## What this pass does and does not close

Folded in as INSTANCES of the invariant, not as drive-bys:

1. **F-1** — the vocabulary gap above. The fix refines the shape so
   that a wrapped-arrow function value is distinguishable from a raw
   one, and `topLevelDefConvention` derives the annotation from it.
2. **F-2 (core)** — the recursor head is emitted SHORT while its
   ctor-order assertion is emitted QUALIFIED. Same shape: two
   emissions about the same object, computed by different paths,
   agreeing only by elaboration accident.
3. **The unused-Pi-binder printer cosmetic** — a named binder nobody
   references should print anonymously. Cosmetic, but it is one of
   the two axes that defeated the F-8 structural gate, so it belongs
   with the emission work rather than in a soundness batch.

Explicitly NOT closed, and named so the pre-release panel can score
it:

- The invariant is stated and given a home; it is **not** enforced by
  construction. There is no `adaptTo`-equivalent that makes a
  signature/body mismatch unrepresentable. Today the enforcement is:
  the shape vocabulary is precise enough for the cases we know, the
  telescope fingerprint refuses a subset of mismatches, and Lean
  rejects the rest loudly. A by-construction chokepoint — annotation
  derived from the body's production record, with the SAWCore type
  as a CHECK rather than an input — is the successor, and it is
  0.03-scale.
- `mkDefinitionWith`'s second caller (`emitImportedRealizationAlias`)
  does not go through `topLevelDefConvention`. That is currently
  fine — an imported-realization alias declares the realization's own
  type, so there is no second authority to disagree with — but it is
  the one live path where the chokepoint is bypassed, and it should
  be re-argued whenever that path grows.
- `BindingShape` remains a three-plus-one enumeration rather than a
  representation type. A shape that carried the full arrow
  convention would make F-1's class unrepresentable; the refinement
  landed here carries only what F-1 needs.
