# Symbolic Termination

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
