# Bisimulation Prover

SAW contains a bisimulation prover to prove that two terms simulate each other.
This prover allows users to prove that two terms executing in lockstep satisfy
some relations over the state of each circuit and their outputs.  This type of
proof is useful in demonstrating the eventual equivalence of two circuits, or
of a circuit and a functional specification.  SAW enables these proofs with the
experimental `prove_bisim` command:

:::{code-block} sawscript
prove_bisim : ProofScript () -> [BisimTheorem] -> Term -> Term -> Term -> Term -> TopLevel BisimTheorem
:::

When invoking `prove_bisim strat theorems srel orel lhs rhs`, the arguments
represent the following:

1. `strat`: A proof strategy to use during verification.
2. `theorems`: A list of already proven bisimulation theorems.
3. `srel`: A state relation between `lhs` and `rhs`.  This relation must have
   the type `lhsState -> rhsState -> Bit`. The relation's first argument is
   `lhs`'s state prior to execution. The relation's second argument is `rhs`'s
   state prior to execution. `srel` then returns a `Bit` indicating whether
   the two arguments satisfy the bisimulation's state relation.
4. `orel`: An output relation between `lhs` and `rhs`.  This relation must have
   the type `(lhsState, output) -> (rhsState, output) -> Bit`. The relation's
   first argument is a pair consisting of `lhs`'s state and output following
   execution. The relation's second argument is a pair consisting of `rhs`'s
   state and output following execution. `orel` then returns a `Bit` indicating
   whether the two arguments satisfy the bisimulation's output relation.
5. `lhs`: A term that simulates `rhs`. `lhs` must have the type
   `(lhsState, input) -> (lhsState, output)`.  The first argument to `lhs` is a
   tuple containing the internal state of `lhs`, as well as the input to `lhs`.
   `lhs` returns a tuple containing its internal state after execution, as well
   as its output.
6. `rhs`: A term that simulates `lhs`. `rhs` must have the type
   `(rhsState, input) -> (rhsState, output)`.  The first argument to `rhs` is a
   tuple containing the internal state of `rhs`, as well as the input to `rhs`.
   `rhs` returns a tuple containing its internal state after execution, as well
   as its output.

On success, `prove_bisim` returns a `BisimTheorem` that can be used in future
bisimulation proofs to enable compositional bisimulation proofs.  On failure,
`prove_bisim` will abort.

## Bisimulation Example

This section walks through an example proving that the Cryptol implementation
of an AND gate that makes use of internal state and takes two cycles to
complete is equivalent to a pure function that computes the logical AND of its
inputs in one cycle. First, we define the implementation's state type:

:::{code-block} cryptol
type andState = { loaded : Bit, origX : Bit, origY : Bit }
:::

`andState` is a record type with three fields:

1. `loaded`: A `Bit` indicating whether the input to the AND gate has been
   loaded into the state record.
2. `origX`: A `Bit` storing the first input to the AND gate.
3. `origY`: A `Bit` storing the second input to the AND gate.

Now, we define the AND gate's implementation:

:::{code-block} cryptol
andImp : (andState, (Bit, Bit)) -> (andState, (Bit, Bit))
andImp (s, (x, y)) =
  if s.loaded /\ x == s.origX /\ y == s.origY
  then (s, (True, s.origX && s.origY))
  else ({ loaded = True, origX = x, origY = y }, (False, 0))
:::

`andImp` takes a tuple as input where the first field is an `andState` holding
the gate's internal state, and second field is a tuple containing the inputs to
the AND gate. `andImp` returns a tuple consisting of the updated `andState` and
the gate's output.  The output is a tuple where the first field is a ready bit
that is `1` when the second field is ready to be read, and the second field
is the result of gate's computation.

`andImp` takes two cycles to complete:

1. The first cycle loads the inputs into its state's `origX` and `origY` fields
   and sets `loaded` to `True`. It sets both of its output bits to `0`.
2. The second cycle uses the stored input values to compute the logical AND.
   It sets its ready bit to `1` and its second output to the logical AND
   result.

So long as the inputs remain fixed after the second cycle, `andImp`'s output
remains unchanged.  If the inputs change, then `andImp` restarts the
computation (even if the inputs change between the first and second cycles).

Next, we define the pure function we'd like to prove `andImp` bisimilar to:

:::{code-block} cryptol
andSpec : ((), (Bit, Bit)) -> ((), (Bit, Bit))
andSpec (_, (x, y)) = ((), (True, x && y))
:::

`andSpec` takes a tuple as input where the first field is `()`, indicating that
`andSpec` is a pure function without internal state, and the second field is a
tuple containing the inputs to the AND function. `andSpec` returns a tuple
consisting of `()` (again, because `andSpec` is stateless) and the function's
output.  Like `andImp`, the output is a tuple where the first field is a ready
bit that is `1` when the second field is ready to be read, and the second field
is the result of the function's computation.

`andSpec` completes in a single cycle, and as such its ready bit is always `1`.
It computes the logical AND directly on the function's inputs using Cryptol's
`(&&)` operator.

Next, we define a state relation over `andImp` and `andSpec`:

:::{code-block} cryptol
andStateRel : andState -> () -> Bit
andStateRel _ () = True
:::

`andStateRel` takes two arguments:

1. An `andState` for `andImp`.
2. An empty state (`()`) for `andSpec`.

`andStateRel` returns a `Bit` indicating whether the relation is satisified.  In
this case, `andStateRel` always returns `True` because `andSpec` is stateless
and therefore the state relation permits `andImp` to accept any state.

Lastly, we define a relation over `andImp` and `andSpec`:

:::{code-block} cryptol
andOutputRel : (andState, (Bit, Bit)) -> ((), (Bit, Bit)) -> Bit
andOutputRel (s, (impReady, impO)) ((), (_, specO)) =
  if impReady then impO == specO else True
:::

`andOutputRel` takes two arguments:

1. A return value from `andImp`. Specifically, a pair consisting of an
   `andState` and a pair containing a ready bit and result of the logical AND.
2. A return value from `andSpec`. Specifically, a pair consisting of an empty
   state `()` and a pair containing a ready bit and result of the logical AND.

`andOutputRel` returns a `Bit` indicating whether the relation is satisfied.  It
considers the relation satisfied in two ways:

1. If `andImp`'s ready bit is set, the relation is satisfied if the output
   values `impO` and `specO` from `andImp` and `andSpec` respectively are
   equivalent.
2. If `andImp`'s ready bit is not set, the relation is satisfied.

Put another way, the relation is satisfied if the end result of `andImp` and
`andSpec` are equivalent.  The relation permits intermediate outputs to differ.

We can verify that this relation is always satisfied--and therefore the two
terms are bisimilar--by using `prove_bisim`:

:::{code-block} sawscript
import "And.cry";
enable_experimental;

and_bisim <- prove_bisim z3 [] {{ andStateRel }} {{ andOutputRel }} {{ andImp }} {{ andSpec }};
:::

Upon running this script, SAW prints:

:::{code-block} console
Successfully proved bisimulation between andImp and andSpec
:::

### Building a NAND gate

We can make the example more interesting by reusing components to build a NAND
gate.  We first define a state type for the NAND gate implementation that
contains `andImp`'s state.  This NAND gate will not need any additional state,
so we will define a type `nandState` that is equal to `andState`:

:::{code-block} cryptol
type nandState = andState
:::

Now, we define an implementation `nandImp` that calls `andImp` and negates the
result:

:::{code-block} cryptol
nandImp : (nandState, (Bit, Bit)) -> (nandState, (Bit, Bit))
nandImp x = (s, (andReady, ~andRes))
  where
    (s, (andReady, andRes)) = andImp x
:::

Note that `nandImp` is careful to preserve the ready status of `andImp`.
Because `nandImp` relies on `andImp`, it also takes two cycles to compute the
logical NAND of its inputs.

Next, we define a specification `nandSpec` in terms of `andSpec`:

:::{code-block} cryptol
nandSpec : ((), (Bit, Bit)) -> ((), (Bit, Bit))
nandSpec (_, (x, y)) = ((), (True, ~ (andSpec ((), (x, y))).1.1))
:::

As with `andSpec`, `nandSpec` is pure and computes its result in a single
cycle.

Next, we define a state relation over `nandImp` and `nandSpec`:

:::{code-block} cryptol
nandStateRel : andState -> () -> Bit
nandStateRel _ () = True
:::

As with `andStateRel`, this state relation is always `True` because `nandSpec`
is stateless.

Lastly, we define an output relation indicating that `nandImp` and `nandSpec`
produce equivalent results once `nandImp`'s ready bit is `1`:

:::{code-block} cryptol
nandOutputRel : (nandState, (Bit, Bit)) -> ((), (Bit, Bit)) -> Bit
nandOutputRel (s, (impReady, impO)) ((), (_, specO)) =
  if impReady then impO == specO else True
:::

To prove that `nandImp` and `nandSpec` are bisimilar, we again use
`prove_bisim`. This time however, we can reuse the bisimulation proof for the
AND gate by including it in the `theorems` paramter for `prove_bisim`:

:::{code-block} sawscript
prove_bisim z3 [and_bisim] {{ nandStateRel }} {{ nandOutputRel }} {{ nandImp }} {{ nandSpec }};
:::

Upon running this script, SAW prints:

:::{code-block} console
Successfully proved bisimulation between nandImp and nandSpec
:::

## Understanding the proof goals

While not necessary for simple proofs, more advanced proofs may require
inspecting proof goals.  `prove_bisim` generates and attempts to solve the
following proof goals:

:::{code-block} text
OUTPUT RELATION THEOREM:
  forall s1 s2 in.
    srel s1 s2 -> orel (lhs (s1, in)) (rhs (s2, in))

STATE RELATION THEOREM:
  forall s1 s2 out1 out2.
    orel (s1, out1) (s2, out2) -> srel s1 s2
:::

where the variables in the `forall`s are:

- `s1`: Initial state for `lhs`
- `s2`: Initial state for `rhs`
- `in`: Input value to `lhs` and `rhs`
- `out1`: Initial output value for `lhs`
- `out2`: Initial output value for `rhs`

The `STATE RELATION THEOREM` verifies that the output relation properly captures
the guarantees of the state relation.  The `OUTPUT RELATION THEOREM` verifies
that if `lhs` and `rhs` are executed with related states, then the result of
that execution is also related.  These two theorems together guarantee that the
terms simulate each other.

When using composition, `prove_bisim` also generates and attempts to solve
the proof goal below for any successfully applied `BisimTheorem` in the
`theorems` list:

:::{code-block} text
COMPOSITION SIDE CONDITION:
  forall g_lhs_s g_rhs_s.
    g_srel g_lhs_s g_rhs_s -> f_srel f_lhs_s f_rhs_s
    where
      f_lhs_s = extract_inner_state g_lhs g_lhs_s f_lhs
      f_rhs_s = extract_inner_state g_rhs g_rhs_s f_rhs
:::

where `g_lhs` is an outer term containing a call to an inner term `f_lhs`
represented by a `BisimTheorem` and `g_rhs` is an outer term containing a call
to an inner term `f_rhs` represented by the same `BisimTheorem`. The variables
in `COMPOSITION SIDE CONDITION` are:

- `extract_inner_state x x_s y`: A helper function that takes an outer term `x`, an
  outer state `x_s`, and an inner term `y`, and returns the inner state of `x_s`
  that `x` passes to `y`.
- `g_lhs_s`: The state for `g_lhs`
- `g_rhs_s`: The state for `g_rhs`
- `g_srel`: The state relation for `g_lhs` and `g_rhs`
- `f_srel`: The state relation for `f_lhs` and `f_rhs`
- `f_lhs_s`: The state for `f_lhs`, as represented in `g_lhs_s` (extracted using
  `extract_inner_state`).
- `f_rhs_s`: The state for `f_rhs`, as represented in `g_rhs_s` (extracted using
  `extract_inner_state`).

The `COMPOSITION SIDE CONDITION` exists to verify that the terms in the
bisimulation relation properly set up valid states for subterms they contain.

## Limitations

For now, the `prove_bisim` command has a couple limitations:

- `lhs` and `rhs` must be named functions.  This is because `prove_bisim` uses
  these names to perform substitution when making use of compositionality.
- Each subterm present in the list of bisimulation theorems already
  proven may be invoked at most once in `lhs` or `rhs`.  That is, if some
  function `g_lhs` calls `f_lhs`, and `prove_bisim` is invoked with a
  `BisimTheorem` proving that `f_lhs` is bisimilar to `f_rhs`, then `g_lhs` may
  call `f_lhs` at most once.
