# Exception hunt — remaining unstated calculus exceptions

2026-07-18. Independent theory audit (fresh-context Fable), user-
commissioned after the domain-map consolidation: are there MORE axes
where scattered hand-rules answer one semantic question? **Answer:
yes — two live families found, both structurally the classifyDomain
disease, neither silently unsound (all divergences loud, divergent
cases corpus-unreachable).** Every other axis swept clean:
adaptation legality (adaptTo IS the sole point-adaptation
chokepoint; all other Pure.pure/Bind.bind are sanctioned emitters),
equality-subject rep, typeArgPositions, Nat dual role, type-
producing/universe analysis, error/effect routing.

## Findings → dispositions

1. **Top-level definition convention (worst — already drifted;
   FIXED 2026-07-18).** §Definitions declared a DefConvention but no
   authority implemented it; three sites open-coded it and diverged:
   translateDefDocWithArity had the wrapped-body annotation clause,
   CryptolModule's "mirror" had silently lost it (stale since
   2026-07-14), SAWModule applied no convention at all. Fixed: new
   single authority `topLevelDefConvention` (Term.hs) — body
   position + annotation carrier — called by all three. Prelude
   auto-emit golden: zero drift (current prelude corpus is Pi/type
   defs).
2. **wrappedHelperFunctionValueSlot/-ResultIsValue do not project D
   (FILED, disposition recorded).** The auditor recommended folding
   into the D-projecting family; REJECTED as stated: this pair is
   the declared callee convention for UseMapsToWrapped helper
   CALLBACKS, whose authority is the support library's Lean
   signatures (Nat callback formals ARE wrapped there — folding to
   D's conditional-Nat would break real genWithProof/iteM
   callbacks). Correct fix shape: reclassify as a bucket-(c)
   declared convention, document its authority (the helper
   signatures) in §Callee Conventions, and align only the
   var-headed arms to D (Prop-kinded family formals raw — currently
   they'd wrap, loud-caught by the backstop). TODO'd.
3. **B-4 (recursorMotiveFunctionConvention.resultPos own dispatch,
   no elimSort)** — already filed 2026-07-18; confirmed unreachable.
4. **propBody quantifier-vs-family Pi discipline (Term.hs ~4365) is
   an unnamed third positional gate** — it answers a
   binder-discipline question D cannot express. FIXED in doc: named
   as the third gate.
5. **RawMotivePosition is load-bearing in adaptTo** (admits
   BindingFunction at a raw position; defensive/unreached) — the
   RawReason label space is NOT fully inert. FIXED in doc: noted.

## Verdict

With Finding 1 fixed and 4/5 documented, the calculus doc is ground
truth for the pre-release soundness audit on every axis EXCEPT the
wrapped-helper callback convention (Finding 2, filed with
disposition) and the filed B-4 latent.
