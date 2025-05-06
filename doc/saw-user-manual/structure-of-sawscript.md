# Structure of SAWScript

SAWScript is a typed functional language with support for sequencing of
imperative commands.

A SAWScript program consists, at the top level, of a sequence of
commands to be executed in order. Each command is terminated with a
semicolon. For example, the `print` command displays a textual
representation of its argument. Suppose the following text is stored in
the file `print.saw`:

:::{code-block} sawscript
print 3;
:::

The command `saw print.saw` will then yield output similar to the
following:

:::{code-block} console
Loading module Cryptol
Loading file "print.saw"
3
:::

The same code can be run from the interactive REPL:

:::{code-block} console
sawscript> print 3;
3
:::

At the REPL, terminating semicolons can be omitted:

:::{code-block} console
sawscript> print 3
3
:::

To make common use cases simpler, bare values at the REPL are treated as
if they were arguments to `print`:

:::{code-block} console
sawscript> 3
3
:::

One SAWScript file can be included in another using the `include`
command, which takes the name of the file to be included as an argument.
For example:

:::{code-block} console
sawscript> include "print.saw"
Loading file "print.saw"
3
:::

Typically, included files are used to import definitions, not perform
side effects like printing. However, as you can see, if any commands
with side effects occur at the top level of the imported file, those
side effects will occur during import.

## Parts of a SAW Script

:::{warning}
This section is under construction!
:::

(first-simple-example)=
## A First Simple Example

:::{warning}
This section is under construction!
:::

To get started with SAW, let's see what it takes to verify simple programs
that do not use pointers (or that use them only internally). Consider,
for instance the C program that adds its two arguments together:

:::{code-block} c
#include <stdint.h>
uint32_t add(uint32_t x, uint32_t y) {
    return x + y;
}
:::

We can specify this function's expected behavior as follows:

:::{code-block} sawscript
let add_setup = do {
    x <- llvm_fresh_var "x" (llvm_int 32);
    y <- llvm_fresh_var "y" (llvm_int 32);
    llvm_execute_func [llvm_term x, llvm_term y];
    llvm_return (llvm_term {{ x + y : [32] }});
};
:::

We can then compile the C file `add.c` into the bitcode file `add.bc`
and verify it with ABC:

:::{code-block} sawscript
m <- llvm_load_module "add.bc";
add_ms <- llvm_verify m "add" [] false add_setup abc;
:::

## Syntax

The syntax of SAWScript is reminiscent of functional languages such as
Cryptol, Haskell and ML. In particular, functions are applied by
writing them next to their arguments rather than by using parentheses
and commas. Rather than writing `f(x, y)`, write `f x y`.

Comments are written as in C, Java, and Rust (among many other languages). All
text from `//` until the end of a line is ignored. Additionally, all
text between `/*` and `*/` is ignored, regardless of whether the line
ends.

## Basic Types and Values

All values in SAWScript have types, and these types are determined and
checked before a program runs (that is, SAWScript is statically typed).
The basic types available are similar to those in many other languages.

- The `Int` type represents unbounded mathematical integers. Integer
  constants can be written in decimal notation (e.g., `42`), hexadecimal
  notation (`0x2a`), and binary (`0b00101010`). However, unlike many
  languages, integers in SAWScript are used primarily as constants.
  Arithmetic is usually encoded in Cryptol, as discussed in the next
  section.

- The Boolean type, `Bool`, contains the values `true` and `false`, like
  in many other languages. As with integers, computations on Boolean
  values usually occur in Cryptol.

- Values of any type can be aggregated into tuples. For example, the
  value `(true, 10)` has the type `(Bool, Int)`.

- Values of any type can also be aggregated into records, which are
  exactly like tuples except that their components have names. For
  example, the value `{ b = true, n = 10 }` has the type `{ b : Bool,
  n : Int }`.

- A sequence of values of the same type can be stored in a list. For
  example, the value `[true, false, true]` has the type `[Bool]`.

- Strings of textual characters can be represented in the `String` type.
  For example, the value `"example"` has type `String`.

- The "unit" type, written `()`, is essentially a placeholder, similar
  to `void` in languages like C and Java. It has only one value, also
  written `()`. Values of type `()` convey no information. We will show
  in later sections several cases where this is useful.

- Functions are given types that indicate what type they consume and
  what type they produce. For example, the type `Int -> Bool` indicates
  a function that takes an `Int` as input and produces a `Bool` as
  output. Functions with multiple arguments use multiple arrows. For
  example, the type `Int -> String -> Bool` indicates a function in
  which the first argument is an `Int`, the second is a `String`, and
  the result is a `Bool`. It is possible, but not necessary, to group
  arguments in tuples, as well, so the type `(Int, String) -> Bool`
  describes a function that takes one argument, a pair of an `Int` and a
  `String`, and returns a `Bool`.

SAWScript also includes some more specialized types that do not have
straightforward counterparts in most other languages. These will appear
in later sections.

## Basic Expression Forms

One of the key forms of top-level command in SAWScript is a _binding_,
introduced with the `let` keyword, which gives a name to a value. For
example:

:::{code-block} console
sawscript> let x = 5
sawscript> x
5
:::

Bindings can have parameters, in which case they define functions. For
instance, the following function takes one parameter and constructs a
list containing that parameter as its single element.

:::{code-block} console
sawscript> let f x = [x]
sawscript> f "text"
["text"]
:::

Functions themselves are values and have types. The type of a function
that takes an argument of type `a` and returns a result of type `b` is
`a -> b`.

Function types are typically inferred, as in the example `f`
above. In this case, because `f` only creates a list with the given
argument, and because it is possible to create a list of any element
type, `f` can be applied to an argument of any type. We say, therefore,
that `f` is _polymorphic_. Concretely, we write the type of `f` as `{a}
a -> [a]`, meaning it takes a value of any type (denoted `a`) and
returns a list containing elements of that same type. This means we can
also apply `f` to `10`:

:::{code-block} console
sawscript> f 10
[10]
:::

However, we may want to specify that a function has a more
specific type. In this case, we could restrict `f` to operate only on
`Int` parameters.

:::{code-block} console
sawscript> let f (x : Int) = [x]
:::

This will work identically to the original `f` on an `Int` parameter:

:::{code-block} console
sawscript> f 10
[10]
:::

However, it will fail for a `String` parameter:

:::{code-block} console
sawscript> f "text"

type mismatch: String -> t.0 and Int -> [Int]
 at "_" (REPL)
mismatched type constructors: String and Int
:::

Type annotations can be applied to any expression. The notation `(e :
t)` indicates that expression `e` is expected to have type `t` and
that it is an error for `e` to have a different type. Most types in
SAWScript are inferred automatically, but specifying them explicitly can
sometimes enhance readability.

Because functions are values, functions can return other functions. We
make use of this feature when writing functions of multiple arguments.
Consider the function `g`, similar to `f` but with two arguments:

:::{code-block} console
sawscript> let g x y = [x, y]
:::

Like `f`, `g` is polymorphic. Its type is `{a} a -> a -> [a]`. This
means it takes an argument of type `a` and returns a _function_ that
takes an argument of the same type `a` and returns a list of `a` values.
We can therefore apply `g` to any two arguments of the same type:

:::{code-block} console
sawscript> g 2 3
[2,3]
sawscript> g true false
[true,false]
:::

But type checking will fail if we apply it to two values of different types:

:::{code-block} console
sawscript> g 2 false

type mismatch: Bool -> t.0 and Int -> [Int]
 at "_" (REPL)
mismatched type constructors: Bool and Int
:::

So far we have used two related terms, _function_ and _command_, and we
take these to mean slightly different things. A function is any value
with a function type (e.g., `Int -> [Int]`). A command is any value with
a special command type (e.g. `TopLevel ()`, as shown below). These
special types allow us to restrict command usage to specific contexts,
and are also _parameterized_ (like the list type). Most but not all
commands are also functions.

The most important command type is the `TopLevel` type, indicating a
command that can run at the top level (directly at the REPL, or as one
of the top level commands in a script file). The `print` command
has the type `{a} a -> TopLevel ()`, where `TopLevel ()` means that it
is a command that runs in the `TopLevel` context and returns a value of
type `()` (that is, no useful information). In other words, it has a
side effect (printing some text to the screen) but doesn't produce any
information to use in the rest of the SAWScript program. This is the
primary usage of the `()` type.

It can sometimes be useful to bind a sequence of commands together. This
can be accomplished with the `do { ... }` construct. For example:

:::{code-block} console
sawscript> let print_two = do { print "first"; print "second"; }
sawscript> print_two
first
second
:::

The bound value, `print_two`, has type `TopLevel ()`, since that is the
type of its last command.

Note that in the previous example the printing doesn't occur until
`print_two` directly appears at the REPL. The `let` expression does not
cause those commands to run. The construct that _runs_ a command is
written using the `<-` operator. This operator works like `let` except
that it says to run the command listed on the right hand side and bind
the result, rather than binding the variable to the command itself.
Using `<-` instead of `let` in the previous example yields:

:::{code-block} console
sawscript> print_two <- do { print "first"; print "second"; }
first
second
sawscript> print print_two
()
:::

Here, the `print` commands run first, and then `print_two` gets the
value returned by the second `print` command, namely `()`. Any command
run without using `<-` at either the top level of a script or within a
`do` block discards its result. However, the REPL prints the result of
any command run without using the `<-` operator.

In some cases it can be useful to have more control over the value
returned by a `do` block. The `return` command allows us to do this. For
example, say we wanted to write a function that would print a message
before and after running some arbitrary command and then return the
result of that command. We could write:

:::{code-block} sawscript
let run_with_message msg c =
  do {
    print "Starting.";
    print msg;
    res <- c;
    print "Done.";
    return res;
  };

x <- run_with_message "Hello" (return 3);
print x;
:::

If we put this script in `run.saw` and run it with `saw`, we get
something like:

:::{code-block} console
Loading module Cryptol
Loading file "run.saw"
Starting.
Hello
Done.
3
:::

Note that it ran the first `print` command, then the caller-specified
command, then the second `print` command. The result stored in `x` at
the end is the result of the `return` command passed in as an argument.

## Other Basic Functions

Aside from the functions we have listed so far, there are a number of other
operations for working with basic data structures and interacting
with the operating system.

The following functions work on lists:

- `concat : {a} [a] -> [a] -> [a]` takes two lists and returns the
concatenation of the two.

- `head : {a} [a] -> a` returns the first element of a list.

- `tail : {a} [a] -> [a]` returns everything except the first element.

- `length : {a} [a] -> Int` counts the number of elements in a list.

- `null : {a} [a] -> Bool` indicates whether a list is empty (has zero
elements).

- `nth : {a} [a] -> Int -> a` returns the element at the given position,
with `nth l 0` being equivalent to `head l`.

- `for : {m, a, b} [a] -> (a -> m b) -> m [b]` takes a list and a
function that runs in some command context. The passed command will be
called once for every element of the list, in order. Returns a list of
all of the results produced by the command.

For interacting with the operating system, we have:

- `get_opt : Int -> String` returns the command-line argument to `saw`
at the given index. Argument 0 is always the name of the `saw`
executable itself, and higher indices represent later arguments.

- `exec : String -> [String] -> String -> TopLevel String` runs an
external program given, respectively, an executable name, a list of
arguments, and a string to send to the standard input of the program.
The `exec` command returns the standard output from the program it
executes and prints standard error to the screen.

- `exit : Int -> TopLevel ()` stops execution of the current script and
returns the given exit code to the operating system.

Finally, there are a few miscellaneous functions and commands:

- `show : {a} a -> String` computes the textual representation of its
argument in the same way as `print`, but instead of displaying the value
it returns it as a `String` value for later use in the program. This can
be useful for constructing more detailed messages later.

- `str_concat : String -> String -> String` concatenates two `String`
values, and can also be useful with `show`.

- `time : {a} TopLevel a -> TopLevel a` runs any other `TopLevel`
command and prints out the time it took to execute.

- `with_time : {a} TopLevel a -> TopLevel (Int, a)` returns both the
original result of the timed command and the time taken to execute it
(in milliseconds), without printing anything in the process.

## REPL Actions

There is an additional class of things that one may type at the REPL
for interactive use:

- `:cd` changes the REPL's current directory.

- `:pwd` prints the REPL's current directory.

- `:env` displays the values and types of all currently bound
variables, including built-in functions and commands.

- `:search` with one or more types (complex types go in parentheses)
searches the currently bound variables, including built-in functions
and commands, and prints those that mention all the types cited.
You can use `_` as a wildcard.
Free type variables are treated as pattern constraints; use
forall-bound type variables using the `{a}` syntax to search
specifically for forall-bound types.

- `:tenv` displays the expansions of all currently defined type
aliases, including those that are built in.

- `:type` or `:t` checks and prints the type of an arbitrary SAWScript
expression:

:::{code-block} console
sawscript> :t show
{a.0} a.0 -> String
:::

- `:help` or `:h` prints the help text for a built-in function or
command:

:::{code-block} console
sawscript> :h show

Description
-----------

    show : {a} a -> String

Convert the value of the given expression to a string.
:::

- `:quit` or `:q` exits the program.

## Further built-in functions and commands

SAW contains many built-in operations, referred to as "primitives."
These appear in SAWScript as built-in functions and commands.
The following sections of the manual will introduce many of these.

## Experimental and deprecated functions and commands

Some of the primitives available in SAW at any given time are
experimental.
These may be incomplete, unfinished, use at your own risk, etc.
The functions and commands associated with these are unavailable
by default; they can be made visible with the `enable_experimental`
command.

Other primitives are considered deprecated.
Some of these, as the
[deprecation process](formal-deprecation-process.md) proceeds, are
unavailable by default.

They can be made visible with the `enable_deprecated` command.
