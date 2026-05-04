/-
Phase 5b / L-discipline-2: end-to-end semantic discharge for the
StreamCorec lowering on `RecOnes.cry`.

The Cryptol property `allTrue = [True] # allTrue` lowers (Phase 5
Slice A) to a `mkStreamFix Bool _ _` whose body uses the
`Stream.rec ... lookup_` pattern to reach prior elements. We
prove the first two values explicitly:

- `streamIdx allTrue 0 = true` (seed value, no recursion exercised)
- `streamIdx allTrue 1 = true` (recursion exercised; the body's
   Stream.rec retrieves the i=0 element via the lookup substitution)

If the lowering broke — e.g., dropped the lookup-form rewrite,
swapped the recursor's case order, or built mkStreamFixPrefix in
the wrong order — these proofs fail. The textual subset
assertions in smoketest + `lake build` cannot catch those (L-16
lesson).

The emitted `RecOnes.allTrue` lives in the module translated by
SAW (see source.txt). `import Emitted` pulls it in verbatim.
-/

import Emitted
import CryptolToLean
import CryptolToLean.SAWCorePrelude_proofs

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePreludeProofs

/-- The seed (i=0) value. Pins the singleton-vec lookup at the
mkStreamFixPrefix base case. After Phase 8's `atWithDefault`
became a structural def, the chain reduces by `simp` + `rfl`. -/
theorem allTrue_at_zero : streamIdx Bool RecOnes.allTrue 0 = Bool.true := by
  unfold RecOnes.allTrue mkStreamFix mkStreamFixIdx mkStreamFixPrefix
  rfl

/-- The first recursive value (i=1). The body's @Stream.rec
retrieves the i=0 prior element via lookup; atWithDefault at
index 1 falls past the 1-element seed vec, so the default —
itself the previous lookup result — is returned. This pins the
lookup substitution: if the translator dropped or mistyped the
substitution, lookup would not return the correct prior value
and the proof would fail. -/
theorem allTrue_at_one : streamIdx Bool RecOnes.allTrue 1 = Bool.true := by
  unfold RecOnes.allTrue mkStreamFix mkStreamFixIdx mkStreamFixPrefix
  rfl
