This test addresses the issue resolved in [#1790](https://github.com/GaloisInc/saw-script/pull/1790). 

In this script, we prove the same theorem - that ```join`{each=32, parts=4, a=Bool} (split x) == x``` - twice; once purely via `z3`, and once via manual rewriting, trying to use the former to prove the latter. 

Lack of type normalization introduces reflexive type coercions in the SAWCore representation of the expression under proof. The manual proof proceeds by eliminating any extant reflexive coercions, then attempting to use the `z3`-proven theorem as a simplification. When no coercions existed in the first place, the simplification applies cleanly. When coercions existed, the simplification does not apply cleanly, since we eliminated them from the goal, but not from the simplification.

Since this proof is possible to resolve in its entirety via evaluation/appeal to `z3`, we need to maintain the core `join` and `split` functions uninterpreted when manually massaging (via `goal_normalize` and `goal_eval_unint`) the goal into a `trivial`ly resolvable form.