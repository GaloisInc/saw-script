(sawscript-intro)=
# Quick Introduction to the SAWScript Language

SAWScript is the metalanguage for the SAW system: it is the framework
used to load specifications, state theorems, set up proofs, and solve
proof goals.
SAW's functionality is, in general, accessed by executing SAWScript
builtins from SAWScript scripts.

One can program in SAWScript; however, ordinary usage does not really
require it; it's generally sufficient to write sequences of builtin
invocations according to the manual and sometimes group them into
blocks.
However, there's enough language involved that we should stop briefly
for a quick introduction and tour.

As discussed in the previous chapter, the most common way to run SAW
(when using SAWScript at all) is on a file of SAWScript code,
although there's also a REPL.
In this chapter we'll outline what goes in those files and just enough
of the syntax and semantics to get started.
A fuller treatment can be found in [a later chapter](#sawscript).

A SAWScript file is a sequence of SAWScript statements executed in
order, top to bottom, each terminated with a semicolon.
Most of the statements you will use are calls to SAWScript builtin
functions, so the first topic is how to call a function.

This script:

:::{code-block} sawscript
print 3;
:::

calls the `print` builtin with the argument `3`, and will print
the following when run:

:::{code-block} console
Loading file "print.saw"
3
:::

Note that there are no parentheses around argument lists like there
are in C and Rust.
The syntax for function calls is like ML and Haskell: you just put
the argument next to the function name.

## Types

The basic types in SAWScript are:

| Name                          | Description    | Example values  |
| ----------------------------- | -------------- | --------------- |
| `Bool`                        | truth values   | `true`, `false` |
| `Int`                         | integers       | `3`             |
| `String`                      | strings        | `"abc"`         |
| `[`_`a`_`]`                   | lists of _`a`_ | `[1, 2, 3]`     |
| `()`                          | unit           | `()`            |
| `(`_`a`_`,` _`b`_`, ...)`     | tuples         | `(1, "abc")`    |
| _`a`_ `->` _`b`_              | functions      | `print`         |

There are many other types, most of them abstract builtin types for
working with different kinds of verification tasks.
These will be introduced in later chapters.

Functions are curried; that means a function of two arguments
is the same type as a function of one argument that returns a
function taking the other argument.

## Looking up Builtins

To look up a builtin, start the REPL and use the `:h` (help) command
with the builtin name:

:::{code-block} console
sawscript> :h print
Description
-----------

    print : {a} a -> TopLevel ()

Print the value of the given expression.
sawscript> 
:::

This gives both the type and the builtin's documentation.
You can use `:t` instead to get just the type.

Here the type is polymorphic: print will take a value of any type
(the syntax `{a}` is a forall-binding, like in Cryptol).

The `TopLevel` annotation in the return type is a monad.

## Monads

SAWScript is a monadic language.
If you have seen programming-language monads (from Haskell or
elsewhere) before, this will be familiar.
If not, don't worry: there's no need to understand how it works under
the covers or at any sort of deep level, and no experience with Haskell
(or for that matter category theory) is needed.

You can think of SAWScript's monads as contexts for code to run in.
There are five of them, all hard-wired, and no facilities for creating
more or doing anything fancy with them.

There are, accordingly, two kinds of builtin.

Builtins that belong to a monad have a return type of the form _`M`_
_`ty`_, where _`M`_ is one of the monads, and the type _`ty`_ is the
function's actual return type.
Thus the `print` builtin shown above executes in the `TopLevel` monad
and returns the unit value `()`.

Builtins that have an ordinary return type are not in any monad
("pure") and can be used anywhere, but are invoked in a slightly
different way, as we'll see in a moment.

For example, the `length` builtin that returns the length of a list:

:::{code-block} console
sawscript> :h length
Description
-----------

    length : {a} [a] -> Int

Compute the length of a list.
sawscript> 
:::

The five SAWScript monads are:

- `TopLevel` is the main monad.
  The syntactic top level, that is, the statements in SAWScript files
  that aren't nested in something else, as well as statements typed
  into the REPL, run in `TopLevel`.

- `ProofScript` is a context for proof tactics.
  Writing your own proof scripts is an advanced topic; see the
  [Interactive Proofs](#interactive-proofs) chapter.

- `LLVMSetup` is a context for assembling specifications for
  LLVM code.

- `JVMSetup` is a context for assembling specifications for
  JVM code.

- `MIRSetup` is a context for assembling specifications for
  MIR (Rust) code.

The tools available in the latter three monads are discussed in the
[Verifying Code](#verifying-code) chapter.
For now, we'll concentrate on `TopLevel`.
The other monads use the same syntax and work in the same way.

Because of the monads there are two ways to call a function.

A pure function like `length` that isn't in a monad is called by
let-binding a variable to hold its return value, then passing it the
right number of arguments:

:::{code-block} sawscript
let x = length [2, 4, 6];
:::

This will bind a new variable `x` and store 3 in it.

A pure "function" that doesn't take any arguments is just a value.
The boolean constants `true` and `false` are examples.

Meanwhile, a function in a monad is called by using `<-` instead of
`let`:

:::{code-block} sawscript
thm <- prove_print z3 {{ 1 < 2 }};
:::

This calls the solver z3 to prove that 1 is less than 2 (more on this
soon) and returns a theorem value, which we save in a new variable
`thm`.

If you don't want the return value, because you don't need it or
because it's `()`, you can throw it away by binding it to `_`.
You can also leave off the `<-` entirely and just call the function:

:::{code-block} sawscript
_ <- print 3;
print 3;
:::

You can think of `<-` as executing the monad function on its right
hand side.
(What it actually does is give it the current context to run in.
Thus, you can't use `<-` with functions in other monads, only the
one you're currently in.
So you can only use `TopLevel` functions at the top level, and you
can't use `TopLevel` functions when assembling an LLVM specification
in `LLVMSetup`.)

A monad function that takes no arguments does nothing until it's
executed with `<-`.

## `return`

The `return` builtin is a monad function that takes an argument and
hands it back when executed.
Thus these statements are equivalent:

:::{code-block} sawscript
let x = 3;
x <- return 3;
:::

Note though that, confusingly, `return` is _not_ a control-flow
operator; it just creates a monad function out of an ordinary
value.
Blame Haskell (where it originated) for the confusion.

## `do` Blocks

One can group a series of statements into a nested block.
The syntax for this is `do {` _`statement...`_ `}`; hence these
are called `do` blocks.
A do-block is a monad function that takes no arguments.
The last entry in a `do` block must be an expression without a
variable binding; it produces a result value for the block.
It will often be the `return` builtin; this is how the name
originated.

The statements in a `do` block must all be in the same monad, but
it can be any monad.
To write an LLVM specification using the `LLVMSetup` monad, write a
`do` block using the `LLVMSetup` builtins (as noted before, these are
introduced in the
[Verifying Code](#verifying-code) chapter)
and, to avoid trying to execute it in `TopLevel`, let-bind it
rather than using `<-`.

Thus for example:

:::{code-block} sawscript
let spec = do {
   llvm_execute_func [];
   return ();
};
:::

The last statement produces `()` as the result value for the block, which
is what's expected for these specifications.

Here `spec` gets bound to a no-arguments monad function of type
`LLVMSetup ()`, which can then be passed in for verification.
The verification backend creates and applies the `LLVMSetup` context
needed to execute it.

This works the same way for the other setup monads.

## Expressions

The arguments to functions are expressions, not statements.
The right-hand side of a `let` statement is also an expression.
Thus calls to pure functions can appear as arguments to functions
(you'll need parentheses to group them).
Calls to monadic functions cannot.
You must execute the monadic function with `<-` and bind the result to
a new variable, then pass the variable as the argument expression.

There is one exception to this: when the argument is itself supposed to
be a monadic function.
In this case you should pass the monadic function itself without executing
it with `<-`.
This comes up with the `ProofScript` arguments to verification functions
as well as the `LLVMSetup`/`JVMSetup`/`MIRSetup` specification blocks.
Builtins like these that take monadic functions directly execute them
themselves at the proper point.

SAWScript also has no infix operators; expressions are basically either
literals of various kinds or function calls.
Computations are done in Cryptol.

## Common Pitfalls

Because functions are curried, missing arguments are not an error; instead
you get a function value back.
If you didn't intend this it will cause potentially confusing type errors
downstream.

Another common problem is to accidentally leave off the semicolon at
the end of a statement, especially one that's a function call.
If the next line is also a function call, it and its arguments will be
interpreted as excess arguments to the first function, also producing
potentially confusing type errors.

## The REPL

The REPL accepts statements in `TopLevel`.
(There is also a `ProofScript` REPL, but that's an advanced topic.)
You may leave off the semicolons at the ends of statements.

Currently it does not accept pure expressions.
This is a shortcoming related to ongoing cleanup of the internals and
will eventually be fixed.
As a workaround, pure expressions can be evaluated at the REPL by
passing them to `return` or `print`:

:::{code-block} sawscript
sawscript> return (length [2, 4, 6])
3
sawscript> 
:::

## Experimental and Deprecated Builtins

Some of the primitives available in SAW at any given time are
experimental.
These may be incomplete, unfinished, use at your own risk, etc.
They may also be unstable and change type or behavior in future
releases.
The functions and commands associated with these are unavailable
by default; they can be made visible with the `enable_experimental`
command.

Other primitives are considered deprecated.
Some of these, as the
[deprecation process](appendices/formal-deprecation-process.md) proceeds, are
unavailable by default.

They can be made visible with the `enable_deprecated` command.


## Haskell-Relative Notes

Haskell veterans will want to know that SAWScript is eagerly evaluated,
not lazily, even though it's monadic.
For non-Haskell folks, this basically means that execution works the
way you expect and things never happen out of order.
