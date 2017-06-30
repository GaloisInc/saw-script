# Overview

There are a few limitations on the types of code that SAW can process.
Some of these limitations arise from the impossibility of automatically
deciding certain theoretical problems, and some arise more narrowly from
the specific analysis algorithms that we have chosen to use.

Ultimately, due to several closely related theoretical results (known as
the halting problem, Rice's theorem, Gödel's completeness theorem, among
others), there will always be *some* combination a program a property
that a given automated analysis system cannot prove. But we have some
flexibility to decide which sorts of programs and properties we can
prove and which we cannot.

SAW builds on two fundamental technologies at the moment, and inherits
the benefits and limitations of both. These two technologies are 1)
symbolic execution with path merging, and 2) SAT and SMT solvers.

The use of symbolic execution limits the style of *loops* SAW can
handle. And the use of SAT and SMT limits the sorts of data structures
SAW can handle in initial and final states of a program. In addition to
these broader limitations, there are some specific details of the Java
and LLVM languages that are not currently supported, but that could be
supported in the future.

At the most abstract level, the two key restrictions are these:

  * All loops must iterate only a finite, fixed number of times during
    execution of the program, based on the specific inputs to the
    symbolic execution process (some of which may be constant values
    rather than symbolic variables).

  * All programs must have initial states and final states that consist
    of a finite, fixed number of bits. Linked lists and dynamic memory
    allocation, for example, are supported, but only in a limited way.
    For instance, a program can take a linked list as input but only if
    the number of elements in that list and the arrangement of pointers
    is known and specified in advance.

The rest of this document describes these limitations in more detail.

# Finite Loops

The standard approach to symbolic execution involves forward execution
of a program with symbolic values. At each branch, the symbolic
execution engine executes *both* alternatives. And, in our
implementation, when reaching a point that both branches must ultimately
lead to (a *post-dominator* of the branch), we merge the symbolic states
created for each branch. Because SAW operates on programs in the JVM or
LLVM languages, which are unstructured control-flow graphs, loops are
just a specific case of branches.

In the most straightforward implementation, this would mean that
symbolic execution of a program containing loops would never terminate.
In SAW, there are two mechanisms, one always enabled and one optional,
that allow some loops to terminate.

The first mechanism is automated simplification of expressions during
symbolic execution. If the value of a variable is constant and it is
updated according to an operation entirely of constants, the result will
still be constant. And comparison between constants will yield a
constant result. And, when SAW executes a conditional branch, it first
checks to see whether the condition is equal to the constant `true` or
`false`. If it is, SAW will execute only one of the branches. So, for
example, a loop that counts from the constant 1 to the constant 10 will
terminate.

The second mechanism, which can be enabled or disabled, is the use of a
SAT solver to determine whether branch conditions are semantically
equivalent to `true` or `false`, even if they are not syntactically
equivalent. For example, consider a loop that counts from `x` to `y`,
where both are input variables, but inside a conditional that guarantees
that `y - x` is less than 10. This loop is also guaranteed to terminate
after 10 iterations, but it requires deeper reasoning to determine that
it will. Enabling path satisfiability checking will allow SAW to
terminate when analyzing this program.

So, as a general rule, if symbolic execution does not seem to be
terminating on the program under analysis, consider enabling branch
satisfiability checking.

TODO: specifics on how to enable path sat checking, how to know if
symbolic execution isn't terminating.

# Fixed-size Inputs and Outputs

The second major limitation in SAW is that the inputs and outputs of
symbolic execution need to have fixed size. In a more concrete technical
sense, this means that each pointer used in a program must either be
considered to be pre-allocated to point to a constant-sized object
before symbolic execution, or point to a constant-sized object allocated
during execution. In practice, this primarily means that arrays must
have constant sizes and that internal pointers (pointer or object fields
of structs or classes) must point to something specific. The only values
allowed to be symbolic during execution are those of scalar variables,
arrays, or scalar fields of aggregate types. The one exception is that,
in LLVM, a pointer may be symbolic if it will never be dereferenced
during the execution of the code being analyzed.

It is worth noting that the restriction to fixed-size inputs and outputs
is actually a necessary consequence of the treatment of loops within
SAW. If a loop must terminate after a fixed number of iterations, it can
access only a finite portion of a heap data structure (even if, in
theory, that data structure extends beyond the portion accessed).

# Other Generic Limitations

Neither the Java or the LLVM simulation support handling of exceptions.
Java programs can throw exceptions, but they are treated as simulation
failures. Verification of a method that throws an exception includes
proving that the path resulting in the exception is infeasible.

Floating point calculations are only supported on concrete values in
Java. Symbolic execution will fail if it encounters floating point
operations on symbolic values. For LLVM, floating point is not supported
at all.

In general, I/O is not supported. Simple printing (`printf` or
`System.out.println`) does work, but other I/O operations will generally
lead to failure of symbolic execution. To analyze code that performs I/O
in some way, it is sometimes possible to create overrides for the I/O
functions or methods. These overrides might assume, for instance, that a
`read` call always reads 10 bytes and that the values of these bytes are
completely arbitrary.

Similarly, code that performs system calls is generally not supported.

# Other Java Limitations

In Java, there is no way to specify the contents of arrays of
references. Such arrays can be used internally in computations, but
there's no way to write a specification for a method that takes them as
input or produces them as output.

Multi-dimensional arrays are not supported.

Native methods are generally not supported, unless there's a special
case in the simulator to provide alternative semantics for them. The
methods currently supported by the simulator include:

* TODO

# Other LLVM Limitations

Only a subset of the LLVM intrinsic functions are supported. These
include:

* TODO

Casts between pointers and integers are limited. The constant 0 is
allowed to be a value of pointer type, and it is never equal to any
non-zero pointer. Pointers can be cast to integers only for temporary
storage and subsequent conversion back to pointer type without
modification. (TODO: is addition or subtraction allowed on a
pointer-as-integer?)
