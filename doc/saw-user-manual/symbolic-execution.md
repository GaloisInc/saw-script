# Introduction to Symbolic Execution

Analysis of Java and LLVM in SAW relies heavily on *symbolic
execution*, so some background on how this process works can help with
understanding the system and its behavior.
If you are already reasonably familiar with symbolic execution and its
concepts and limitations, you can safely skip this chapter.

At the most abstract level, symbolic execution works like normal
program execution except that program values can be *symbolic*:
instead of a single concrete value like `3`, a value can be a symbol
that stands for any value of the proper type, or a subset of those
values, or an expression in terms of such symbols.
Typically we create fresh symbols to serve as the program input, and
then as symbolic execution executes, new values are computed from old
ones and are processed as expressions in terms of those input symbols.
Thus a single symbolic execution is equivalent to doing many concrete
executions at once.
(Ideally, one symbolic execution covers all possible concrete executions,
but as we'll see it isn't quite that simple.)

Consider the following C function that returns the maximum of two values:

:::{code-block} c
unsigned int max(unsigned int x, unsigned int y) {
    if (y > x) {
        return y;
    } else {
        return x;
    }
}
:::

If you call this function with two concrete inputs and assign the
result, like this:

:::{code-block} c
int r = max(5, 4);
:::

then it will assign the value `5` to `r`.
Now, however, we can create two fresh symbols `a` and `b` and call the
function with them as the arguments:

:::{code-block} c
int r = max(a, b);
:::

The symbolic value that we store in `r` is some form of the expression
`if b > a then b else a`, possibly specifically the C expression
`b > a ? b : a` and possibly something slightly different.

(Aside: whether symbolic expressions inside a symbolic execution
engine are represented in the input language or some other language is
a design decision.
The tradeoffs involved are well beyond the scope of this introduction.)

To generate this expression, however, you will note that we have to
execute both branches of the `if` statement in the original function.
Any concrete execution can evaluate the `if` condition to either 0 or
1 and then execute one branch of the if and not the other.
However, during symbolic execution the if condition is the symbolic
expression `b > a`, which could be either true or false.
Therefore we need to proceed down both branches of the if.
This in turn produces (in general) two different program states
afterward, which then need to be merged back together.
This merge applies the if condition to the results of each side, and
introduces the if that appears in our symbolic result.

You will have noticed that the symbolic expression we get from calling
`max` with arbitrary inputs is scarcely different from the original
code; this is because `max` is a very simple function and we have used
the most simple possible input context.

## Path Satisfiability

Suppose, however, that we already knew something about the inputs before
calling the function.
Consider this calling context instead:

:::{code-block} c
int minmax(unsigned int x, unsigned int y) {
    int r;

    if (x > y) {
        r = max(x, y);
    } else {
        r = min(x, y);
    }
    return r;
:::

(This is perhaps a silly function to write, but it will serve as an
example.)

If in turn we call this with symbolic inputs `a` and `b`, when we
get to `max` we know that `a > b`, because we're inside the first
branch of the `if` in `minmax`.
This expression (that tells us what must be true to get where we
are) is called the *path condition* because it's associated with
the execution path that we took to get to the current program point.

Now when we reach the `if` in `max`, it checks `b > a`.
We can conclude that this is false: there is no satisfying assignment
that makes `a > b && b > a` true.
We can therefore skip the true branch of the `if` entirely; the
symbolic return value we get from `max` is just `a`.
What we have just done is called *path satisifiability checking*:
checking whether a path that we're proposing to take (the true branch
of the `if` in `max`) is reachable, which is true if and only if the
complete path condition is satisfiable.

Assuming similar logic in `min`, the overall symbolic result
we get from `minmax` is `if a > b then a else a`, which the symbolic
execution engine will likely simplify further to just `a`.
As noted, it's a silly function.
But don't assume that path satisfiability is trivial.
Every `assert` has a branch inside it, and the side of the branch
that aborts is supposed to be unreachable.
Detecting when it isn't is one of the primary applications of symbolic
execution.
 
## Symbolic Termination

Programs that contain loops create additional challenges.
When we reach the condition of a loop, unless we can determine that
the condition is definitely false, we generate two cases: one where
the loop ends and one where we go around the loop again.
This means that unless the symbolic program state evolves to a
configuration where the condition is definitely false, we will keep
generating more cases where we go around the loop again, and do so
forever.

Loops that reach a definitely false state are said to *symbolically
terminate*.
For example, loops with concrete, constant bounds symbolically
terminate: if the count starts at 0, and goes up by one on each
loop iteration, and the condition is, say, `i < 15`, after unrolling
the loop fifteen times `i` will be `15` and we stop.

Other loops may also symbolically terminate.
The following contrived example symbolically terminates, because as
it goes it accumulates (in its path condition) assertions about
successive values of `i` not being zero mod 8.
Because 5 and 8 are relatively prime, it will eventually accumulate
all 8 possible values, of which one must be zero; at that point there
is no satisfying assignment for `i` that continues the loop (this is
within the ability of a solver to discover) and we stop.

:::{code-block} c
uint8_t f(uint8_t i) {
  int done = 0;
  while (!done) {
    if (i % 8 == 0) done = 1;
    i += 5;
  }
  return i;
}
:::

Counting loops with symbolic bounds in general do not symbolically terminate.
However, loops with symbolic bounds where the symbolic bound also in
turn has a concrete bound do.

:::{code-block} c
for (i = 0; i < n; i++) {
    // do something
}
:::

Given a concrete bound on `n`, there are only a finite number of
values it can take, and consequently there are also a finite number of
values for `i`, and eventually we exhaust them all.
If `i` and `n` are math integers or bignums, this loop will never
symbolically terminate without an explicit constraint on `n`.
If (as in C code) they are machine integers, however, it will, because
there is then an implicit maximum value for `n`.
However, this will evaluate the loop as many times as there are positive
machine integers of the type (less 1) which may be prohibitively slow
and functionally equivalent to nontermination.

The inability to handle unbounded loops is a fundamental limitation of
symbolic execution.
(In program analysis terms, symbolic execution is *precise* but not
*complete*.)

There are several approaches commonly taken in practice to approximate
the behavior of unbounded loops and still get useful proof results.
SAW's support for these is discussed in later chapters.

<!--
   XXX: this section used to mention the effects of turning path
   satisfiability checking on:
   
   : Normally, most of the Java and LLVM analysis commands simply compare
   : branch conditions to the constant `True` or `False` to determine whether
   : a branch may be feasible. However, each form of analysis allows branch
   : satisfiability checking to be turned on if needed, in which case
   : functions like `f` above will terminate.

   This needs to get stuffed in somewhere later. It also needs to be
   recast as turning path satisfiability _off_, because "normally" it
   should be on. Turning it off is an advanced feature and you need to
   know what you're doing.

   (Though now we've at least introduced what path satisfiability
   checking _is_, which was missing before.)
-->

## Setting up Symbolic Execution

A symbolic execution system is very similar to an interpreter, just
one has a different notion of what constitutes a value and executes
*all* paths through the program instead of just one.

The process of writing a specification for a piece of code is thus
similar to building a test harness for that same code.

More specifically, the setup process for a test harness typically takes
the following form:

1. Initialize or allocate any resources needed by the code.
   This typically means allocating memory and setting the
   initial values of variables.

2. Execute the code.

3. Check the desired properties of the system state after the code
   completes.

Accordingly, three pieces of information are particularly relevant to
the symbolic execution process, and are therefore needed as input to the
symbolic execution system:

- The initial (potentially symbolic) state of the system.

- The code to execute.

- The final state of the system, and which parts of it are relevant to
  the properties being tested.

In the next chapter, we'll describe how SAW's symbolic execution support
operates in the context of these key concepts.
