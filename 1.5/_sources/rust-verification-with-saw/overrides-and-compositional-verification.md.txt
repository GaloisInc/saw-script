# Overrides and compositional verification

Up until this point, all uses of `mir_verify` in this tutorial have provided an
empty list (`[]`) of overrides. This means that any time SAW has simulated a
function which calls another function, it will step into the definition of the
callee function and verify its behavior alongside the behavior of the callee
function. This is a fine thing to do, but it can be inefficient. For example,
consider a function like this:

:::{literalinclude} code/overrides.rs
:lines: 5-9
:language: rust
:::

Here, the caller function `f` invokes the callee function `g` three separate
times. If we verify `f` with `mir_verify` as we have done up until this point,
then SAW must analyze the behavior of `g` three separate times. This is
wasteful, and especially so if `g` is a large and complicated function.

This is where _compositional verification_ enters the picture. The idea behind
compositional verification is that when we prove properties of a caller
function, we can reuse properties that we have already proved about callee
functions. These properties are captured as _override specifications_, which
are also referred to by the shorthand term _overrides_. When a caller invokes a
callee with a corresponding override specification, the override's properties
are applied without needing to re-simulate the entire function.

As it turns out, the command needed to produce an override specification is
already familiar to us—it's `mir_verify`! If you examine the type of this
command:

:::{code-block} console
sawscript> :type mir_verify
MIRModule -> String -> [MIRSpec] -> Bool -> MIRSetup () -> ProofScript () -> TopLevel MIRSpec
:::

The returned value is a `MIRSpec`, which captures the behavior of the function
that was verified as an override spec. This override can then be passed to
another call to `mir_verify` to use as part of a larger proof.

Let's now try compositional verification in practice. To do so, we will first
prove a spec for the `g` function above. For demonstration purposes, we will
pick a simplistic implementation of `g`:

:::{literalinclude} code/overrides.rs
:lines: 1-3
:language: rust
:::

Note that we don't really _have_ to use compositional verification when `g` is
this simple, as SAW is capable of reasoning about `g`'s behavior directly when
proving a spec for `f`. It's still worth going along with this exercise,
however, as the same principles of compositional verification apply whether the
implementation of `g` is small or large.

The first step of compositional verification is to prove a spec for `g`, the
callee function:

:::{literalinclude} code/overrides.saw
:lines: 3-11
:language: sawscript
:::

There's nothing that different about this particular proof from the proofs
we've seen before. The only notable difference is that we bind the result of
calling `mir_verify` to a `MIRSpec` value that we name `g_ov` (short for "`g`
override"). This part is important, as we will need to use `g_ov` shortly.

The next step is to write a spec for `f`. Since `g` adds `1` to its argument,
`f` will add `3` to its argument:

:::{literalinclude} code/overrides.saw
:lines: 13-19
:language: sawscript
:::

Again, nothing too surprising. Now let's prove `f` against `f_spec` by using
`g_ov` as a compositional override:

:::{literalinclude} code/overrides.saw
:lines: 21
:language: sawscript
:::

Here, note that instead of passing an empty list (`[]`) as we have done before,
we now pass a list containing `g_ov`. This informs `mir_verify` that whenever
it simulates a call to `g`, it should reuse the properties captured in `g_ov`.
In general, we can pass as many overrides as we want (we will see examples of
this later in the tutorial), but for now, one override will suffice.

Let's run the proof of `f` against `f_spec`, making sure to pay attention to
the output of SAW:

:::{code-block} console
[19:06:17.392] Verifying overrides/96c5af24::f[0] ...
[19:06:17.406] Simulating overrides/96c5af24::f[0] ...
[19:06:17.407] Matching 1 overrides of  overrides/96c5af24::g[0] ...
[19:06:17.407] Branching on 1 override variants of overrides/96c5af24::g[0] ...
[19:06:17.407] Applied override! overrides/96c5af24::g[0]
[19:06:17.407] Matching 1 overrides of  overrides/96c5af24::g[0] ...
[19:06:17.407] Branching on 1 override variants of overrides/96c5af24::g[0] ...
[19:06:17.407] Applied override! overrides/96c5af24::g[0]
[19:06:17.407] Matching 1 overrides of  overrides/96c5af24::g[0] ...
[19:06:17.407] Branching on 1 override variants of overrides/96c5af24::g[0] ...
[19:06:17.407] Applied override! overrides/96c5af24::g[0]
[19:06:17.407] Checking proof obligations overrides/96c5af24::f[0] ...
[19:06:17.422] Proof succeeded! overrides/96c5af24::f[0]
:::

We've now proven `f` compositionally! The first two lines ("`Verifying ...`"
and "`Simulating ...`") and the last two lines ("`Checking proof obligations
...`" and "`Proof succeeded! ...`") are the same as before, but this time, we
have some additional lines of output in between:

* Whenever SAW prints "`Matching <N> overrides of <function>`", that's when you
  know that SAW is about to simulate a call to `<function>`. At that point, SAW
  will check to see how many overrides (`<N>`) for `<function>` are available.
* Whenever SAW prints "`Branching on <N> override variants of <function>`", SAW is
  trying to figure out which of the `<N>` overrides to apply. In this example,
  there is only a single override, so the choice is easy. In cases where there
  are multiple overrides, however, SAW may have to work harder (possibly even
  consulting an SMT solver) to figure out which override to use.
* If SAW successfully picks an override to apply, it will print
  "`Applied override! ...`".

In the example above, we used a single `g` override that applies for all
possible arguments. In general, however, there is no requirement that overrides
must work for all arguments. In fact, it is quite common for SAW verification
efforts to write different specifications for the same function, but with
different arguments. We can then provide multiple overrides for the same
function as part of a compositional verification, and SAW will be able to pick
the right override depending on the shape of the argument when invoking the
function being overridden.

For example, let's suppose that we wrote different `g` specs, one where the
argument to `g` is even, and another where the argument to `g` is odd:

:::{literalinclude} code/overrides.saw
:lines: 23-42
:language: sawscript
:::

We can then prove `f` compositionally by passing both of the `g` overrides to
`mir_verify`:

:::{literalinclude} code/overrides.saw
:lines: 43
:language: sawscript
:::

Like before, this will successfully verify. The only different now is that SAW
will print output involving two overrides instead of just one:

:::{code-block} console
[20:48:07.649] Simulating overrides/96c5af24::f[0] ...
[20:48:07.650] Matching 2 overrides of  overrides/96c5af24::g[0] ...
[20:48:07.650] Branching on 2 override variants of overrides/96c5af24::g[0] ...
[20:48:07.652] Applied override! overrides/96c5af24::g[0]
...
:::

Keep in mind that if you provide at least one override for a function as part
of a compositional verification, then SAW _must_ apply an override whenever it
invokes that function during simulation. If SAW cannot find a matching
override, then the verification will fail. For instance, consider what would
happen if you tried proving `f` like so:

:::{literalinclude} code/overrides-fail.saw
:lines: 31
:language: sawscript
:::

This time, we supply one override for `g` that only matches when the argument
is even. This is a problem, as SAW will not be able to find a matching override
when the argument is odd. Indeed, SAW will fail to verify this:

:::{code-block} console
[20:53:29.588] Verifying overrides/96c5af24::f[0] ...
[20:53:29.602] Simulating overrides/96c5af24::f[0] ...
[20:53:29.602] Matching 1 overrides of  overrides/96c5af24::g[0] ...
[20:53:29.602] Branching on 1 override variants of overrides/96c5af24::g[0] ...
[20:53:29.603] Applied override! overrides/96c5af24::g[0]
[20:53:29.603] Matching 1 overrides of  overrides/96c5af24::g[0] ...
[20:53:29.603] Branching on 1 override variants of overrides/96c5af24::g[0] ...
[20:53:29.604] Applied override! overrides/96c5af24::g[0]
[20:53:29.604] Matching 1 overrides of  overrides/96c5af24::g[0] ...
[20:53:29.604] Branching on 1 override variants of overrides/96c5af24::g[0] ...
[20:53:29.605] Applied override! overrides/96c5af24::g[0]
[20:53:29.605] Symbolic simulation completed with side conditions.
[20:53:29.606] Checking proof obligations overrides/96c5af24::f[0] ...
[20:53:29.623] Subgoal failed: overrides/96c5af24::f[0] No override specification applies for overrides/96c5af24::g[0].
Arguments:
- c@26:bv
Run SAW with --sim-verbose=3 to see a description of each override.
[20:53:29.623] SolverStats {solverStatsSolvers = fromList ["SBV->Z3"], solverStatsGoalSize = 388}
[20:53:29.624] ----------Counterexample----------
[20:53:29.624]   x: 1
...
Proof failed.
:::

Here, we can see that `No override specification applies`, and SAW also
generates a counterexample of `x: 1`. Sure enough, `1` is an odd number!

## Overrides and mutable references

Compositional overrides provide great power, as they effectively allow you to
skip over certain functions when simulating them and replace them with simpler
implementations. With great power comes great responsibility, however. In
particular, one must be careful when using overrides for functions that modify
mutable references. If an override does not properly capture the behavior of a
mutable reference, it could potentially lead to incorrect proofs.

This is the sort of thing that is best explained with an example, so consider
these two functions:

:::{literalinclude} code/overrides-mut.rs
:lines: 1-9
:language: rust
:::

The `side_effect` function does not return anything interesting; it is only
ever invoked to perform a side effect of changing the mutable reference `a` to
point to `0`. The `foo` function invokes `side_effect`, and as a result, it
will always return `0`, regardless of what the argument to `foo` is. No
surprises just yet.

Now let's make a first attempt at verifying `foo` using compositional
verification. First, we will write a spec for `side_effect`:

:::{literalinclude} code/overrides-mut-fail.saw
:lines: 3-8
:language: sawscript
:::

`side_effect_spec` is somewhat odd. Although it goes through the effort of
allocating a mutable reference `a_ref` and initializing it, nothing about this
spec states that `a_ref` will point to `0` after the function has been invoked.
This omission is strange, but not outright wrong—the spec just underspecifies
what the behavior of the function is. Indeed, SAW will successfully verify this
spec using `mir_verify`:

:::{literalinclude} code/overrides-mut-fail.saw
:lines: 16
:language: sawscript
:::

Next, let's try to write a spec for `foo`:

:::{literalinclude} code/overrides-mut-fail.saw
:lines: 10-14
:language: sawscript
:::

At this point, alarm bells should be going off in your head. This spec
incorrectly states that `foo(x)` should return `x`, but it should actually
return `0`! This looks wrong, but consider what would happen if you tried to
verify this compositionally using our `side_effect_ov` override:

:::{literalinclude} code/overrides-mut-fail.saw
:lines: 17
:language: sawscript
:::

If SAW were to simulate `foo(x)`, it would invoke create a temporary variable
`b` and assign it to the value `x`, and then it would invoke `side_effect(&mut
b)`. At this point, the `side_effect_ov` override would apply. According to
`side_effect_spec`, the argument to `side_effect` is not modified at all after
the function returns. This means that when the `foo` function returns `b`, it
will still retain its initial value of `x`. This shows that if we were to use
`side_effect_ov`, we could prove something that's blatantly false!

Now that we've made you sweat a little bit, it's time for some good news: SAW
won't _actually_ let you prove `foo_spec`. If you try this compositional proof
in practice, SAW will catch your mistake:

:::{code-block} console
[14:50:29.170] Verifying overrides_mut/11e47708::foo[0] ...
[14:50:29.181] Simulating overrides_mut/11e47708::foo[0] ...
[14:50:29.181] Matching 1 overrides of  overrides_mut/11e47708::side_effect[0] ...
[14:50:29.181] Branching on 1 override variants of overrides_mut/11e47708::side_effect[0] ...
...
State of memory allocated in precondition (at overrides-mut-fail.saw:6:12) not described in postcondition
:::

The line of code that SAW points to in the "`State of memory ...`" error
message is:

:::{literalinclude} code/overrides-mut-fail.saw
:lines: 4
:language: sawscript
:::

SAW informs us that although we allocated the mutable reference `a_ref`, we
never indicated what it should point to after the function has returned. This
is an acceptable (if somewhat unusual) thing to do when verifying
`side_effect_spec` using `mir_verify`, but it is _not_ acceptable to do this
when using this spec as an override. To avoid unsound behavior like what is
described above, any override that allocates a mutable reference in its
preconditions _must_ declare what its value should be in the postconditions, no
exceptions.

Thankfully, repairing this spec is relatively straightforward. Simply add a
`mir_points_to` statement in the postconditions of `side_effect_spec`:

:::{literalinclude} code/overrides-mut.saw
:lines: 3-11
:language: sawscript
:::

Then use the correct return value in `foo_spec`:

:::{literalinclude} code/overrides-mut.saw
:lines: 13-19
:language: sawscript
:::

And now the compositional proof of `foo_spec` works!

## Unsafe overrides

Now that we've made it this far into the tutorial, it's time to teach you a
more advanced technique: _unsafe_ overrides. Up until this point, we have
relied on SAW to check all of our work, and this is usually what you'd want
from a formal verification tool. In certain circumstances, however, it can be
useful to say "I know what I'm doing, SAW—just believe me when I say this spec
is valid!" In order to say this, you can use `mir_unsafe_assume_spec`:

:::{code-block} console
sawscript> :type mir_unsafe_assume_spec
MIRModule -> String -> MIRSetup () -> TopLevel MIRSpec
:::

`mir_unsafe_assume_spec` is `mir_verify`'s cousin who likes to live a little
more dangerously. Unlike `mir_verify`, the specification that you pass to
`mir_unsafe_assume_spec` (the `MIRSetup ()` argument) is _not_ checked for full
correctness. That is, `mir_unsafe_assume_spec` will bypass SAW's usual symbolic
execution pipeline, which is why one does not need to pass a `ProofScript`
argument (e.g., `z3`) to `mir_unsafe_assume_spec`. SAW will believe whatever
spec you supply `mir_unsafe_assume_spec` to be valid, and the `MIRSpec` that
`mir_unsafe_assume_spec` returns can then be used in later compositional
verifications.

Why would you want to do this? The main reason is that writing proofs can be
difficult, and sometimes, there are certain functions in a SAW verification
effort that are disproportionately harder to write a spec for than others. It
is tempting to write specs for each function in sequence, but this can run the
risk of getting stuck on a particularly hard-to-verify function, blocking
progress on other parts of the proofs.

In these situations, `mir_unsafe_assume_spec` can be a useful prototyping tool.
One can use `mir_unsafe_assume_spec` to assume a spec for the hard-to-verify
function and then proceed with the remaining parts of the proof. Of course, you
should make an effort to go back and prove the hard-to-verify function's spec
later, but it can be nice to try something else first.

For example, here is how one can unsafely assume `g_spec` and use it in a
compositional proof of `f_spec`:

:::{literalinclude} code/overrides-unsafe.saw
:lines: 19-20
:language: sawscript
:::

It should be emphasized that when we say "`unsafe`", we really mean it.
`mir_unsafe_assume_spec` can be used to prove specs that are blatantly wrong,
so use it with caution.
