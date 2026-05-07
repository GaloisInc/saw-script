# Symbolic Execution

Analysis of Java and LLVM within SAWScript relies heavily on *symbolic
execution*, so some background on how this process works can help with
understanding the behavior of the available built-in functions.

At the most abstract level, symbolic execution works like normal program
execution except that the values of all variables within the program can be
arbitrary *expressions*, potentially containing free variables, rather than
concrete values. Therefore, each symbolic execution corresponds to some set
of possible concrete executions.

As a concrete example, consider the following C program that returns
the maximum of two values:

:::{code-block} c
unsigned int max(unsigned int x, unsigned int y) {
    if (y > x) {
        return y;
    } else {
        return x;
    }
}
:::

If you call this function with two concrete inputs, like this:

:::{code-block} c
int r = max(5, 4);
:::

then it will assign the value `5` to `r`. However, we can also consider what
it will do for *arbitrary* inputs. Consider the following example:

:::{code-block} c
int r = max(a, b);
:::

where `a` and `b` are variables with unknown values. It is still
possible to describe the result of the `max` function in terms of `a`
and `b`. The following expression describes the value of `r`:

:::{code-block} text
ite (b > a) b a
:::

where `ite` is the "if-then-else" mathematical function, which based on
the value of the first argument returns either the second or third. One
subtlety of constructing this expression, however, is the treatment of
conditionals in the original program. For any concrete values of `a` and
`b`, only one branch of the `if` statement will execute. During symbolic
execution, on the other hand, it is necessary to execute *both*
branches, track two different program states (each composed of symbolic
values), and then *merge* those states after executing the `if`
statement. This merging process takes into account the original branch
condition and introduces the `ite` expression.

A symbolic execution system, then, is very similar to an interpreter
that has a different notion of what constitutes a value and executes
*all* paths through the program instead of just one. Therefore, the
execution process is similar to that of a normal
interpreter, and the process of generating a model for a piece of code
is similar to building a test harness for that same code.

More specifically, the setup process for a test harness typically takes
the following form:

1. Initialize or allocate any resources needed by the code. For Java and
   LLVM code, this typically means allocating memory and setting the
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

In the following sections, we describe how the Java and LLVM analysis
primitives work in the context of these key concepts. We start with the
simplest situation, in which the structure of the initial and final
states can be directly inferred, and move on to more complex cases that
require more information from the user.

## Symbolic Termination

Above we described the process of executing multiple branches and
merging the results when encountering a conditional statement in the
program. When a program contains loops, the branch that chooses to
continue or terminate a loop could go either way. Therefore, without a
bit more information, the most obvious implementation of symbolic
execution would never terminate when executing programs that contain
loops.

The solution to this problem is to analyze the branch condition whenever
considering multiple branches. If the condition for one branch can never
be true in the context of the current symbolic state, there is no reason
to execute that branch, and skipping it can make it possible for
symbolic execution to terminate.

Directly comparing the branch condition to a constant can sometimes be
enough to ensure termination. For example, in simple, bounded loops like
the following, comparison with a constant is sufficient.

:::{code-block} c
for (int i = 0; i < 10; i++) {
    // do something
}
:::

In this case, the value of `i` is always concrete, and will eventually
reach the value `10`, at which point the branch corresponding to
continuing the loop will be infeasible.

As a more complex example, consider the following function:

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

The loop in this function can only be determined to symbolically
terminate if the analysis takes into account algebraic rules about
common multiples. Similarly, it can be difficult to prove that a base
case is eventually reached for all inputs to a recursive program.

In this particular case, however, the code _is_ guaranteed to terminate
after a fixed number of iterations (where the number of possible
iterations is a function of the number of bits in the integers being
used). To show that the last iteration is in fact the last possible one,
it's necessary to do more than just compare the branch condition with a
constant. Instead, we can use the same proof tools that we use to
ultimately analyze the generated models to, early in the process, prove
that certain branch conditions can never be true (i.e., are
_unsatisfiable_).

Normally, most of the Java and LLVM analysis commands simply compare
branch conditions to the constant `True` or `False` to determine whether
a branch may be feasible. However, each form of analysis allows branch
satisfiability checking to be turned on if needed, in which case
functions like `f` above will terminate.

Next, we examine the details of the specific commands available to
analyze JVM and LLVM programs.
