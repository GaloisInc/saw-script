# Getting Started

For your very first proof, start the `saw` executable as described in
the previous section, and then at the REPL (the `sawscript>` prompt) type
the following:
```sawscript
prove_print z3 {{ 2 < 3 }};
```

This asks SAW to prove, using the Z3 solver, that 2 is less than 3.
This in turn is not a very difficult proof, so SAW will in response
immediately print something like the following:
```console
[18:00:00.000] Theorem (EqTrue
  (ecLt Integer PCmpInteger
     (ecNumber (TCNum 2) Integer PLiteralInteger)
     (ecNumber (TCNum 3) Integer PLiteralInteger)))
```
where the timestamp in `[]` is the current time in UTC, the word
`Theorem` indicates what you got, and the rest is a rendering of the
theorem statement `2 < 3` into SAW's internal interchange language
called SAWCore.

Note that you do _not_ need to be able to read the SAWCore version of
the theorem statement except for certain very advanced uses of SAW.
(Nonetheless we hope to make it more readable in the future...)

Let's take a closer look at exactly what this operation does.
First, the `prove_print` command is a SAWScript builtin that asks
SAW to prove some proposition (the second argument) using some
solver or proof script (the second argument) and print the result.

For the proof script we just use the builtin tactic `z3` that runs the
Z3 solver.
The proposition `{{ 2 < 3 }}` is a Cryptol code block containing a
simple Cryptol expression.
In SAWScript, Cryptol expressions can be embedded in double curly
braces like this.

Now try asking for something that isn't true:
```sawscript
prove_print z3 {{ 3 < 2 }};
```
This will fail, print a stack trace (which is not super helpful in this
context, but can be important in a large proof development), as well as
`prove: 1 unsolved subgoals`, meaning that it couldn't prove `{{ 3 < 2 }}`,
plus also `Invalid: []`, which means that the overall proof attempt failed.

The empty list in the `Invalid` result is, in general, a counterexample
for which the proposition isn't true.
In this case because everything is a constant, the counterexample is
empty.

That isn't very interesting, so let's try something else not true:
```sawscript
prove_print z3 {{ \(x: [8]) (y: [8]) -> x < y }};
```
The proposition should be read as "for all `x` and `y`, `x < y`."
That is obviously not true, so we get a failure, and a counterexample
with values of `x` and `y` for which it's not true: `Invalid: [x = 0,
y = 0]`.

Here the `[8]` clauses are a type annotations to specify that `x` and
'y' should be treated as 8-bit bitvectors.
If you leave this off, the type is ambiguous and SAW rejects the proof.
Unfortunately, as of the current writing, it does so with the following
mysterious and entirely unhelpful complaint:
```sawscript
prove_print z3 {{ \x y -> x < y }};
```
produces
```console
sequentToSATQuery: expected EqTrue, actual:
isort 0
```
See [issue #1418](https://github.com/GaloisInc/saw-script/issues/1418).

## Proofs About Code

While proving arbitrary Cryptol propositions is an important use case,
SAW is perhaps most commonly used to do proofs about code.
These proofs have a somewhat different form.

Under normal circumstances, proofs about code in SAW are done via
symbolic execution.
SAW uses the Crucible symbolic execution engine to run the code
against arbitrary ("symbolic") inputs, and checks that this execution
matches a specification written in terms of preconditions and
postconditions.

These specifications are assembled using SAWScript; then one fires off
the proof itself using one of several SAWScript functions.

For a simple example, place the following C code in a file called `example.c`:
```C
int clamp(int x) {
   return x > 100 ? 100 : x;
}
```
Then compile it as follows:
```sh
clang -emit-llvm -c example.c -o example.bc
```
This produces an LLVM bitcode file that SAW can read.

Now place the following in a file `example.saw`:
```sawscript
bc <- llvm_load_module "example.bc";

let clamp_spec = do {
   x <- llvm_fresh_var "x" (llvm_int 32);
   llvm_execute_func [llvm_term x];
   llvm_return (llvm_term {{ if x > 100 then 100 else x }});
};

llvm_verify bc "clamp" [] true clamp_spec z3;
```
<!--
XXX: that isn't tested yet because of the apple clang issue, come back after
XXX: fetching the fix
-->
Now run `saw` on the script file:
```sh
saw example.saw
```
It should print `Verifying clamp...`, then `Simulating clamp...` (this is the
symbolic execution stage), then `Checking proof obligations clamp...` (this is
checking the conditions identified by the symbolic execution that are needed
for success), then `Proof succeeded! clamp`.

To see what it does if the code doesn't match the specification, change the
`x > 100` in `example.saw` to `x > 101`.
The proof will fail, and provide you with a counterexample: the specification
and the code do not match when `x` is 100.

Now, let's unpack what this example does.
The C code contains a simple function `clamp` that takes an integer argument,
and returns the argument value, clamping it to no greater than 100.

The first step in the script loads the LLVM bitcode we generated with `clang`.
This is done with the SAWScript builtin `load_llvm_module`; it returns a handle
that we remember as `bc` for "bitcode".

The next part of the SAW script is the specification:
```sawscript
let clamp_spec = do {
   x <- llvm_fresh_var "x" (llvm_int 32);
   llvm_execute_func [llvm_term x];
   let x' = {{ if x > 100 then 100 else x }};
   llvm_return (llvm_term x');
};
```

The name `clamp_spec` is arbitrary, although it's usually helpful to name
specifications after the code they specify.
The `do` block is a series of actions that we associate with these names.
First, we call `llvm_fresh_var` to allocate a variable for use in the
specification.
Variables allocated with `llvm_fresh_var` like this become inputs to
the verification.
They are forall-quantified in the resultant theorem.
Here we pass it the string `"x"` as a name for SAW to use when talking
to us; `x` is arbitrary but as with the specification name it's
usually helpful to name specification objects after their
corresponding code objects.
Meanwhile, then unquoted `x` on the left is the SAWScript-level variable
we store the result in.
The argument `llvm_int 32` is the LLVM-level type for the variable, in
this case a 32-bit bitvector.
This corresponds to the C type `int` used in the C code.

The second step is that we call the function we're verifying, and pass
it a list of arguments.
In this case we have one argument, `llvm_term x`.
The use of `llvm_term` promotes `x`, which is a Cryptol-level value,
to an LLVM-level value.
See [XXX](XXX).

The third step is to figure the return value we want to specify.
We bind it to the name `x'`.
The difference between the first line, which sets `x` using the
syntax `x <- ...`, and this line, which sets `x'` using the syntax
`let x' = ...`, is that the `<-` form is monadic.
In the `<-` form, the right-hand side is executed in some monad and
the result is bound to the variable `x`.
In the `let` form, the right-hand side is evaluated purely, and not
executed in any monad.
See [XXX](XXX) for further information.

The final step of the specification is to specify the return value.
Again we use `llvm_term` to lift the Cryptol-level value to an
LLVM-level value.

Having written the specification, we now apply by verifying it
against the function `clamp` in the bitcode module `bc`.

```SAWScript
llvm_verify bc "clamp" [] true z3;
```
Here `bc` is the LLVM bitcode module and `"clamp"` is the function
within it we want to verify.
The empty list `[]` is a list of other previously verified functions
we want to use as lemmas for verifying this function.
Our simple example function does not call any other functions, so
we provide nothing here.
In more complex verifications there will often be entries here.
See [XXX](XXX).

The `true` enables _path satifiability checking_.
This prevents SAW from exploring certain cases of impossible execution.
In simple code like this, it has no effect; in other cases it avoids
spurious verification failures.
In some cases with complex code path satisfiability checking can
become combinatorially expensive, and in some of those cases disabling
it avoids the consequent performance problems and still successfully
verifies the code without generating spurious failures.
See [XXX](XXX).
In general best practice is to enable path satisfiability checking,
and only turn it off if complications ensue.

Finally, the last argument is a proof script or solver to use to
solve the proof goals that result from symbolic execution.

## Further Examples

For further worked examples, please consult one or both of the
SAW tutorials:
LLVM/Java Verification with SAW
and
Rust Verification with SAW
that you can find alongside this manual.

There is also a collection of examples in the `examples` subtree of the
source repository.

## Remainder of this Guide

The remainder of this user guide is organized by topic, introducing
various concepts and functionality relevant to SAW users.

<!--
XXX: Go through this and sprinkle forward references, certainly
XXX: all the XXX ones but probably quite a few more.
XXX: I'm putting this off because a lot of the references we ought
XXX: to have don't have targets yet, or the targets are misnamed or
XXX: in the wrong place.
-->
