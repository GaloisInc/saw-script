# Coherence audit — position/callee domain classification

2026-07-17. Independent theory audit (fresh-context Fable auditor),
commissioned when the Either@core design scoping
(`2026-07-17_either-stream-recursor-convention.md`) surfaced an
asymmetry between the function-result and recursor-motive rules for
variable-headed types. Brief: is the calculus's domain
classification ONE map, or scattered predicates that can disagree?

**Thesis: CONFIRMED.** ~8 hand-written cascades each re-answer
"value or raw?" by re-walking the same head dispatch
(`asSort → asEq → asPi → isCryptolNumType → asNatType →
var-headed tail`). They agree on every concrete type class and
diverge ONLY on variable-headed types — at exactly the hand-copied
final arm, mediated by two different recognizers (`isVariableHead`,
no kind check, vs `isVariableHeadTypeFamily`). That is the
historical seam-bug generator; the Either@core reject is one
instance.

## Site enumeration

(paths `saw-core-lean/src/SAWCoreLean/`; line refs at audit time)

| # | Site | Location | Emits |
|---|------|----------|-------|
| S1 | `shouldWrapBinder` | Convention.hs:762 | base value test (every tail calls it) |
| S2 | `bindingShapeOfType` | Convention.hs:709 | BindingShape over self-emitted Lean types |
| S3 | `instantiationMode` | Term.hs:732 | ArgMode for type actuals |
| S4 | `phaseBetaArgModesFor.modeFor` | Term.hs:771 | ArgMode, raw-target primitives |
| S5 | `phaseBetaFunctionValueModesFor.modeFor` | Term.hs:824 | ArgMode, phase-β fn values |
| S6 | `natValueResult` | Term.hs:847 | Nat-from-value-input |
| S7 | `phaseBetaResultIsValue` | Term.hs:868 | THE function-result rule |
| S8 | `functionConventionValueSlot` | Term.hs:965 | fn binder slot |
| S9 | `functionConventionResultIsValue` | Term.hs:982 | recursor-field test (misnamed) |
| S10 | `recursorMotiveResultPosition` | Term.hs:1014 | THE recursor-result rule |
| S11 | `recursorMotiveFunctionConvention.resultPos` | Term.hs:1055 | delegates to S7 |
| S12 | `standaloneEqualitySubjectRep` | Term.hs:2113 | operand-domain-directed (the one RIGHT design) |

## Disagreement table (domain answer per type class)

Coherent everywhere except (b) Nat, (g) bare sort-0 type variable,
(h) applied var-headed family:

- **(b) Nat — PRINCIPLED, recorded, consistent.** Raw as
  input/index/binder; value as a computed result (S7 via
  `natValueResult`, S10 via non-Prop elimSort). The exemplar of
  legitimate position-dependence.
- **(g) bare sort-0 var — IRREGULAR, rank #1.** Every site says
  VALUE except S10 (`isVariableHeadTypeFamily` arm →
  `ExpectRaw RawValuePosition`, Term.hs:1026). This is the
  Either@core hole. Failure mode today: LOUD over-rejection
  (Term.hs:3521,3563 fire precisely on wrapped-scrutinee ×
  raw-result). Candidate A's semantic call is correct.
- **(h) applied var family `p y pf` — IRREGULAR the other way,
  rank #2, NOT fixed by candidate A.** S10 says RAW; S1/S5/S7/S8/S9
  say VALUE. The only recorded principle (Term.hs:101-116:
  "wrapping would force a universe constraint that doesn't hold
  polymorphically") supports RAW — so the SHIPPING function-result
  value-classification may be the over-approximation (the dual of
  the six under-approximation seam bugs). No `adaptTo` bypass found
  (loud if reachable), but not exhaustively ruled out. Lower
  reachability (needs a type that IS an applied var family —
  higher-order proof-carrying territory).
- **Rank #3 — internal recursor split.** S10 (motive `\i -> a` →
  raw) vs S11 (motive `\i -> (x -> a)` → result value, via S7):
  same var-headed codomain, opposite answer across an intervening
  Pi. Structural root: the two recognizers.

## Doc-vs-code

Nat rule: doc states it, code matches. Equality-subject
operand-domain rule: doc states it, code matches (S12 — single
authority, the pattern to copy). **The var-headed domain rule is
absent from `2026-07-02_position-callee-calculus.md` entirely** —
the code invented two answers because the authority is silent.
Root defect.

## Architecture verdict

Refactor to ONE shared domain classifier; candidate A is the right
decision for cell (g) but the wrong shape to land it in:

```haskell
data Domain = DValue | DRawType | DRawProp | DFunction | DNum
            | DNat | DVarHeaded VarHeadedKind   -- Bare | AppliedFamily
classifyDomain :: Term -> Domain
-- position enters ONLY as explicit projections:
domainArgMode        :: Domain -> ArgMode
domainBinderPosition :: [TypeIx] -> Int -> Domain -> ExpectedPosition
domainResultPosition :: ResultCtx -> Domain -> ExpectedPosition
--   ResultCtx = { elimSort, computedFromValueInput }
```

Recommendations:
1. Take candidate A's semantic call (bare-var motive → value).
2. Land it through the shared classifier, not as a seventh
   hand-arm.
3. Resolve (h) EXPLICITLY first: applied var family raw-everywhere
   (honor the universe principle; fix S7/S8/S9) or value-everywhere
   (drop the principle; sound only if sort-0 binders cannot be
   Prop-instantiated — the companion audit's sort/cumulativity
   probe decides). Do not merge candidate A while (h) is unstated.
4. Add the missing var-headed section to the calculus doc.

## Session synthesis (2026-07-17)

Course adopted pending the companion rule-change audit
(sort/cumulativity + reachability probes): shared-domain-map
consolidation with the Either@core fix falling out of it; the (h)
principle decision goes to the user with both audits in hand.
