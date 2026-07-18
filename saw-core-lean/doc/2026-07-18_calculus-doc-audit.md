# Calculus-doc coherence audit (post-domain-map amendment)

2026-07-18. Independent theory audit of the updated
`2026-07-02_position-callee-calculus.md` (the canonical domain-map
section added 2026-07-17) for internal coherence and doc-vs-code
agreement. **VERDICT: COHERENT-WITH-FIXES — no soundness blockers.**
All fixes applied same-day; residual nits filed in TODO.md.

## Verified

- `classifyDomain` matches the documented `D(tau)` on every arm.
- Prop backstop CONFIRMED end-to-end: `PropSort <= _ = True`
  (Functor.hs:66) admits Prop-instantiation; `wrapExcept` is the
  SOLE wrapping carrier and every value route (`Bind.bind`,
  `Pure.pure`, motive body wraps) goes through `Except String _`,
  so the ill-typed-at-Prop backstop fires uniformly. No silent
  path.
- Recursor motives always emit via `translateMotiveAtConvention`
  (dispatch position nParams), never the generic type-producing
  lambda path — the M-1 divergence (below) was latent, not live.
- isort/qsort flags strip to TypeSort (`asSort`); advisory only.
- The 10 review questions are not stale; an 11th (domain
  projection) was added.

## Findings → dispositions

- **M-1 (gate item, FIXED):** `Term.hs` generic type-producing
  lambda still hand-composed
  `shouldWrapBinder && not isVariableHeadTypeFamily` — the last
  surviving scattered cascade. Proven equivalent to
  `classifyDomain body == DValue` and rewritten as that projection
  with the undirected-type-family principle stated in-source.
- **A-1 (FIXED, doc):** the dependency/index positional gate
  legitimately shadows `D`; the doc now names the ONLY two
  shadowing gates (dependency/index; recursor elimSort).
- **A-2 (FIXED, doc):** only `isVariableHead` is retired;
  `isVariableHeadTypeFamily` survives as a kind-based recognizer in
  orthogonal type-producing checks, never a wrap authority — doc
  corrected.
- **A-3 (FIXED, doc):** only `Eq`-shaped propositions are
  domain-classified raw; non-`Eq` constant-headed propositions ride
  the backstop (loud) — now stated.
- **B-1 (FIXED, doc):** term-level-variable-head sub-case
  (`DValue`) added to the `D(x args)` table.
- **B-2 (FIXED, code):** `DVarRaw` Haddock's dead "not a family we
  can commit to" clause removed; Prop-kinded heads are the only
  production.
- **B-3 (FILED):** raw-REASON labels under Prop elimination are
  inconsistent across proposition-class domains
  (RawValuePosition vs RawPropositionPosition) — emission-neutral
  (`R(Raw*,tau)=T(tau)`); pick role-reflecting reasons.
- **B-4 (FILED):** `recursorMotiveFunctionConvention.resultPos`
  re-walks its own head dispatch and omits the elimSort gate —
  unreachable (Prop-elim forces a Prop-valued motive), but should
  project `D`.
- **C-nit (FILED):** pin `wrapExcept` as the sole wrapper via a
  smoketest source lint so the Prop backstop is tamper-evident.
