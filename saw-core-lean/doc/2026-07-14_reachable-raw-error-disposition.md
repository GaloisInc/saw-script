# Reachable raw `error` disposition (OP-2 rider audit + design note)

**Date**: 2026-07-14. **Status**: IMPLEMENTED (same day) — independent
audit (independent session) UPHELD all three rules with conditions;
implementation followed the audit record exactly
(`translateRawPositionError` in Term.hs; `translateRawErrorObligation`
deleted; smoketest re-pointed; `saw-boundary/raw_error_rejection`
pins rule 2; polynomial t1 golden refreshed sorry-free under rule 1;
the rule-1 message slot adapts through the wrapped carrier like every
`UseArgWrapped` slot). Companion to
`2026-07-12_obligation-placement-design.md` (OP-2 implementation
record's rider census, which this completes and corrects).

## Audit record (2026-07-14, independent; verdicts folded in)

- **Rule 1 UPHELD** — no force-without-apply witness exists in
  SAWCore: `errorOp` raises the moment the applied error value is
  demanded to WHNF (`Simulator/Prims.hs:1479`, `Simulator.hs:688`),
  no `VFun` is ever produced for a function-typed error, and function
  values are eliminated only by application (`Value.hs:310`; no
  seq/strict-force in Prelude.sawcore). Laziness aligns on both
  sides. THREE CONDITIONS: (1) non-dependent final result only
  (t1 satisfies: codomain `Except String (Stream Bool)` closed under
  the Nat binder; checkable via asPi + free-var test); (2) binder
  carriers must be POSITION-DIRECTED, not uniformly wrapped (t1's
  domain is raw `Nat`; the `Bool -> Bool` probe's domain is wrapped);
  (3) the message must route through the existing
  `mapsToWrapped … saw_throw_error` lowering — NOTE: the current raw
  path DROPS SAW's message entirely (the dispatch discards `_msg`),
  so rule 1 is a strict improvement over the status quo.
- **Rule 2 UPHELD** — calculus-mandated (§296-311: no silent `A` at
  raw type/proof/proposition/motive/index positions); decidable
  position-locally from `resultTy` shape alone. Since the translator
  never holds a proof of absurdity and never reduces recursors,
  EVERY raw-result error is reachable by this note's definition —
  rule 2 collapses to "reject all raw-result error" and rule 3 never
  fires. Known limitation (accepted): a genuinely-dead branch routed
  through a raw-result error now rejects the whole def where it
  previously emitted-with-sorry; no sound capability is lost (the
  sorry artifact was never completable).
- **Rule 3 → DELETE, don't guard**: `translateRawErrorObligation` is
  dead after rules 1-2 (its remaining trigger is never produced and
  not decidable at the handler position). `rawErrorResultShape`
  STAYS (reused by if0NatRaw and raw-fix).
- **CENSUS CORRECTION**: four real emitters, not one — polynomial t1
  PLUS `obligations/raw_error_{nat,prop,function}` (their pins live
  in `expected.txt` contains-directives, which a `*.lean`-only grep
  misses). Disposition: `raw_error_nat` (raw Nat) and
  `raw_error_prop` (proof) and `raw_error_function`
  (`Nat -> Nat`, raw final result) all become rule-2 rejections;
  polynomial t1's TCInf handler becomes rule-1 constant-error.
- **Smoketest re-pointing correction**: the `Bool -> Bool` probe has
  a WRAPPED final result (`Bool`) — it becomes a rule-1
  `saw_throw_error Bool` constant function, NOT a rejection. The
  Nat / Sort / Eq probes become rule-2 rejection assertions. No
  retained direct probe of the False contract — nothing emits it.
- **OP-2 message-exactness CONFIRMED** for the wrapped route
  (`saw_throw_error α msg = Bind.bind msg Except.error` — SAW's own
  payload, no novel strings).

## Rider audit: the full census

`translateRawErrorObligation` (Term.hs) is the single emitter of the
`h_raw_error_ : False` contract: raw-position `Prelude.error`
(Nat/index, type, proof, or function result) emits a local `False`
obligation and produces the raw value through `False.elim`.

Every position in the corpus that carries it (grep over all emitted
`*.lean` + `*.lean.good`, 2026-07-14):

1. **Four smoketest litmus probes** ("Prelude.error raw/type/proof/
   function results emit obligations", SmokeTest.hs): bare
   `Prelude.error` at Nat, `Sort 0`, `Eq Bool True False`, and
   `Bool -> Bool`. These are DELIBERATE direct probes of the contract
   mechanics — the error is the entire term, "reachability" is not a
   claim they make. They stay.
2. **One real position**: `saw-boundary/polynomial_literal_rejection/
   polynomial_literal.t1.lean.good` — the `Num.rec` TCInf case
   handler of `TestLit_Poly1`.

No other artifact in the corpus emits the contract. The audit
therefore reduces to position 2.

## Finding: the one real position is REACHABLE

The 2026-07-12 rider census called this position "dead for finite
`Num` but reachable if a caller instantiates `TCInf`". The audit
sharpens that: `TestLit_Poly1` is emitted as

```lean
noncomputable def TestLit_Poly1 (u1218 : Num) : Except String (…) :=
  @Num.rec (…)
    (fun η_arg_0 η_arg_1 => Pure.pure (bvNat η_arg_0 η_arg_1)) -- TCNum
    (let h_raw_error_obligation_ : (Prop) := (False);
     let h_raw_error_ : … := ((by sorry));
     @False.elim (Nat -> Except String (Stream Bool)) h_raw_error_)
    u1218 (…)
```

`u1218 : Num` is a def PARAMETER. Any Lean consumer may apply
`TestLit_Poly1 Num.TCInf` and select the `False.elim` branch. That is
not unreachable-with-context — the context is a top-level parametric
def, and the artifact can never be completed sorry-free (no proof of
`False` exists). Loud, sound (nothing kernel-checks with `sorryAx`),
but exactly the "sound but undischargeable" family OP-1/OP-2 exist to
eliminate, and a direct violation of the rider's bar: "a REACHABLE
raw `Prelude.error` must reject per the calculus rather than emit an
undischargeable `False`."

Reachability rule the audit supports: **eliminator case-handler
positions count as reachable** unless the scrutinee is a closed
constructor application in the same emitted term. The translator does
not reduce recursors, and emitted defs are the export surface — a
handler's reachability is decided by the def's own signature, not by
how SAW happened to instantiate it upstream.

## The missed third option: Pi-typed error with a wrapped codomain

The reject-vs-keep-False dichotomy in the OP-2 follow-up misses that
THIS position (and every recursor handler whose motive result is a
function into a wrapped carrier) has a FAITHFUL lowering that needs
no obligation at all:

SAW's `error` at type `Nat -> [inf][1]`-shape means "the function
whose every application errors" — SAW's lazy semantics only observe
`error` when the application is forced. The Phase-β carrier for the
codomain is `Except String (Stream Bool)`; the faithful translation
is the constantly-erroring function

```lean
fun (_ : Nat) => (saw_throw_error (Stream Bool) "<SAW's message>"
                    : Except String (Stream Bool))
```

- Error semantics land exactly where SAW's do: at application/force
  time, through the same `saw_throw_error` route every wrapped-value
  `error` already takes (OP-2 message-exactness applies verbatim —
  the string is SAW's own error payload, nothing novel).
- No obligation, no `sorry`, no `False` — the artifact elaborates and
  can complete.
- `TestLit_Poly1 Num.TCInf n` evaluates to `Except.error …`, which IS
  the SAW meaning of forcing an `[inf]`-width polynomial literal.

Generalization: `Prelude.error` at a Pi type eta-lowers through the
binders until the result position is reached; if the result position
is wrapped (value domain), emit the nested-lambda constant error at
the wrapped result. This is a POSITION-DIRECTED rule: it needs the
expected position of the error term (which the translator now always
has), not a syntactic special case.

## Proposed disposition (three rules, replacing the blanket contract)

1. **Pi-typed `error` whose result position is wrapped**: eta-lower
   to the constant-error function (above). No obligation. This covers
   the polynomial t1 position and un-blocks its family without any
   trust cost.
2. **Raw-result `error` (Nat/index, type, proof, or raw-result Pi)
   at a REACHABLE position** (top-level results, formal-parameter-
   scrutinee eliminator handlers, anything a consumer can select):
   REJECT at translation with a named diagnostic
   (`raw error at reachable position <role>`), per the calculus.
   Rejection is not a coverage regression the release cares about:
   after rule 1, the corpus has NO real instance of this class.
3. **Raw-result `error` at a genuinely unreachable-with-context
   position** (closed-constructor scrutinee in the same term — not
   currently emitted by any path, since the translator does not
   reduce recursors): keep the loud `False` contract, which is the
   correct statement of "this branch needs a proof of absurdity from
   context". The smoketest litmus probes pin the mechanics; their
   direct-error shape becomes rule-2 RE JECT territory, so they must
   be re-pointed at rule assertions (probe expectations change from
   `h_raw_error_obligation_` presence to the named rejection), with
   ONE retained direct probe of the False contract behind the
   unreachable gate if any emitter still reaches it — otherwise the
   contract machinery (`translateRawErrorObligation`) is deleted with
   the rule-2 rejection replacing it.

Net effect on the corpus: polynomial t1 re-emits WITHOUT sorry
(golden refresh, diff review: the TCInf branch becomes a constant
error function); no other artifact changes; smoketest raw-error
probes update to the new expectations; the boundary row family
(`polynomial_literal_rejection`) keeps pinning whatever still
rejects.

## Audit checklist for the reviewer

- Is the constant-error eta-lowering faithful for DEPENDENT Pis?
  (Restriction: apply rule 1 only when the eta-lowered result type is
  closed under the introduced binders' wrapped translation — the
  non-dependent case; dependent function-typed error has no corpus
  witness and falls to rule 2 rejection.)
- Does any SAW-side consumer distinguish `error` at function type
  from `\x -> error`? (SAWCore observes both only by forcing; if a
  probe exists where SAW's evaluator errors WITHOUT application while
  Lean's constant function does not, rule 1 is refuted for that
  probe.)
- Is the OP-2 message-exactness condition satisfied? (The payload is
  SAW's own message; `saw_throw_error` is the established route.)
- Does rule 2's reachability classification need Γ information the
  translator lacks at the error position? (It should not: the
  position/callee calculus already threads the surrounding role.)
