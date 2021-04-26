# Limitations

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [Limitations](#limitations)
    - [Overview](#overview)
    - [Finite Loops](#finite-loops)
    - [Identifying and Resolving Non-Termination](#identifying-and-resolving-non-termination)
    - [Fixed-size Inputs and Outputs](#fixed-size-inputs-and-outputs)
    - [Other Generic Limitations](#other-generic-limitations)
    - [Other Java Limitations](#other-java-limitations)
    - [Other LLVM Limitations](#other-llvm-limitations)
    - [Crucible LLVM Limitations](#crucible-llvm-limitations)

<!-- markdown-toc end -->


## Overview

There are a few limitations on the types of code that SAW can process.
Some of these limitations arise from the impossibility of automatically
deciding certain theoretical problems, and some arise more narrowly from
the specific analysis algorithms that we have chosen to use.

Ultimately, due to several closely related theoretical results (known as
the halting problem, Rice's theorem, Gödel's completeness theorem, among
others), there will always be *some* combination of a program and a
property that a given automated analysis system cannot prove. But we
have some flexibility to decide which sorts of programs and properties
we can prove and which we cannot.

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

## Finite Loops

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

## Identifying and Resolving Non-Termination

To determine whether path satisfiability checking will be helpful when
verification is taking a long time, several debugging flags can help
determine where execution is getting stuck. In general, most cases of
slow verification come from one of three sources: slow execution of
individual instructions, usually due to memory loads or stores at
symbolic addresses; slow execution of an external theorem prover; or
re-executing the body of a loop a large or unbounded number of times.
Path satisfiability checking only affects the last of these three.

The first step in determining what might be causing performance problems
is to trace execution of individual instructions, enabled with the `-d`
flag followed by a specific verbosity level to enable. For the older
LLVM-based interface (`llvm_extract`, `llvm_symexec` and `llvm_verify`)
use `-d2`. For Java analysis, or Crucible-based LLVM analysis, use
`-d4`.

If you see the output pause after execution of a load or store
instruction, then complex symbolic addresses are probably to blame. If
you see the output pause after a return instruction, then a slow
external prover is probably to blame (and it may be worth trying a
different prover). If you see a steady stream of instructions being
executed, however, then either the code being analyzed is large and it
simply hasn't reached the end yet (which could mean that loops have
constant but large iteration bounds), or it could mean that symbolic
execution is getting stuck in an infinite loop. In this case, path
satisfiability checking may allow it to terminate.

## Fixed-size Inputs and Outputs

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

## Other Generic Limitations

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

## Other Java Limitations

In Java, there is no way to specify the contents of arrays of
references. Such arrays can be used internally in computations, but
there's no way to write a specification for a method that takes them as
input or produces them as output.

Multi-dimensional arrays are not supported.

Native methods are generally not supported, unless there's a special
case in the simulator to provide alternative semantics for them. The
methods currently supported by the simulator include:

* `System.out.print`
* `System.out.println`
* `java.lang.Boolean.valueOf`
* `java.lang.Byte.valueOf`
* `java.lang.Short.valueOf`
* `java.lang.Integer.valueOf`
* `java.lang.Long.valueOf`
* `java.lang.Class.desiredAssertionStatus0`
* `java.lang.Class.getClassLoader`
* `java.lang.Class.getComponentType`
* `java.lang.Class.getPrimitiveClass`
* `java.lang.Class.isArray`
* `java.lang.Class.isPrimitive`
* `java.lang.Class.registerNatives`
* `java.lang.ClassLoader.registerNatives`
* `java.lang.Double.doubleToRawLongBits`
* `java.lang.Float.floatToRawIntBits`
* `java.lang.Runtime.gc`
* `java.lang.String.intern`
* `java.lang.StringBuilder.append`
* `java.lang.System.arraycopy`
* `java.lang.System.exit`
* `java.lang.System.nanoTime`
* `java.lang.System.currentTimeMillis`
* `java.lang.System.identityHashCode`
* `java.lang.Thread.registerNatives`
* `java.lang.Throwable.fillInStackTrace`
* `java.io.BufferedOutputStream.flush`
* `java.io.FileInputStream.initIDs`
* `java.io.FileOutputStream.initIDs`
* `java.io.ObjectStreamClass.initIDs`
* `java.io.RandomAccessFile.initIDs`
* `java.security.AccessController.doPrivileged`
* `java.util.Arrays.fill`

## Other LLVM Limitations

Only a subset of the LLVM intrinsic functions are supported. These
include:

* `llvm.bswap.i16`
* `llvm.bswap.i32`
* `llvm.bswap.i48`
* `llvm.bswap.i64`
* `llvm.expect.i32`
* `llvm.expect.i64`
* `llvm.lifetime.start`
* `llvm.lifetime.end`
* `llvm.memcpy.p0i8.p0i8.i32`
* `llvm.memcpy.p0i8.p0i8.i64`
* `llvm.memset.p0i8.i32`
* `llvm.memset.p0i8.i64`
* `llvm.objectsize.i32.p0i8`
* `llvm.objectsize.i64.p0i8`
* `llvm.sadd.with.overflow`
* `llvm.uadd.with.overflow`

And a subset of the C standard library is supported:

* `__assert_fail`
* `__assert_rtn`
* `__memset_chk`
* `__memcpy_chk`
* `alloca`
* `calloc`
* `free`
* `malloc`
* `printf`

Casts between pointers and integers are limited. The constant 0 is
allowed to be a value of pointer type, and it is never equal to any
normal pointer. Pointers can be cast to integers only for temporary
storage and subsequent conversion back to pointer type without
modification.

## Crucible LLVM Limitations

As with the legacy LLVM backend, only certain intrinsics are implemented.
These include:

<!-- This list is generated from the Crucible source code:
     curl https://raw.githubusercontent.com/GaloisInc/crucible/master/crucible-llvm/src/Lang/Crucible/LLVM/Intrinsics.hs | grep "let nm = " | perl -p -i -e 's/let nm = "(.+)" in/\1/' | sort
-->

* `llvm.ctlz.i32`
* `llvm.lifetime.end`
* `llvm.lifetime.start`
* `llvm.memcpy.p0i8.p0i8.i32`
* `llvm.memcpy.p0i8.p0i8.i64`
* `llvm.memmove.p0i8.p0i8.i32`
* `llvm.memmove.p0i8.p0i8.i64`
* `llvm.memset.p0i8.i32`
* `llvm.memset.p0i8.i64`
* `llvm.objectsize.i32.p0i8`
* `llvm.objectsize.i64.p0i8`

And the subset of the C standard library:

* `__assert_rtn`
* `__memcpy_chk`
* `__memset_chk`
* `calloc`
* `free`
* `malloc`
* `memcpy`
* `memmove`
* `memset`
* `printf`
* `putchar`
* `puts`
