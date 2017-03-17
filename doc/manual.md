# Overview

The Software Analysis Workbench (SAW) is a tool for constructing
mathematical models of the computational behavior of software,
transforming these models, and proving properties about them.

SAW can currently construct models of a subset of programs written in
Cryptol, LLVM (and therefore C), and JVM (and therefore Java). The
models take the form of typed functional programs, so in a sense SAW can
be considered a translator from imperative programs to their functional
equivalents. Given a functional model in SAW, various external proof
tools, including a variety of SAT and SMT solvers, can be used to prove
properties about it. Models can be constructed from arbitrary Cryptol
programs, and can typically be constructed from C and Java programs that
have fixed-size inputs and outputs, and that terminate after a fixed
number of iterations of any loop (or a fixed number of recursive calls).

The process of extracting models from programs, manipulating them, and
sending them to external provers is orchestrated using a special purpose
language called SAWScript. SAWScript is a typed functional language with
support for sequencing of imperative commmands.

The rest of this document first describes how SAW can be invoked and
outlines the structure of the SAWScript language and its relationship
with Cryptol. It then follows up with a description of the commands in
SAWScript that can transform functional models (`Term` values) and prove
properties about them. Finally, it describes the specific commands
available for constructing models from imperative programs in a variety
of languages.

# Invoking SAW

The primary mechanism for interacting with SAW is through the `saw`
executable included as part of the standard binary distribution. With no
arguments, `saw` starts a read-evaluate-print loop (REPL) which allows
the user to interactively evaluate commands in the SAWScript language,
described in more detail in the following section. With one file name
argument, it executes the specified file as a SAWScript program.

In addition to a file name, the `saw` executable accepts several
command-line options:

`-h, -?, --help`

  ~ Print a help message.

`-V, --version`

   ~ Show the version of the SAWScript interpreter.

`-c path, --classpath=path`

  ~ Specify a colon-delimited list of paths to search for Java classes.

`-i path, --import-path=path`

  ~ Specify a colon-delimited list of paths to search for imports.

`-t, --extra-type-checking`

  ~ Perform extra type checking of intermediate values.

`-I, --interactive`

  ~ Run interactively (with a REPL).

`-j path, --jars=path`

  ~ Specify a colon-delimited list of paths to `.jar` files to search
  for Java classes.

`-d num, --sim-verbose=num`

  ~ Set the verbosity level of the Java and LLVM simulators.

`-v num, --verbose=num`

  ~ Set verbosity level of the SAWScript interpreter.

It also uses several environment variables for configuration:

`CRYPTOLPATH`

  ~ Specify a colon-delimited list of paths to search for Cryptol
  imports (including the Cryptol prelude).

`SAW_IMPORT_PATH`

  ~ Specify a colon-delimited list of paths to search for imports.

`SAW_JDK_JAR`

  ~ Specify the path of the `.jar` file containing the core Java
  libraries.

All of the command-line options and environment variables that accept
colon-delimited lists use semicolon-delimited lists on Windows.

# Structure of SAWScript

A SAWScript program consists, at the top level, of a sequence of
commands to be executed in order. Each command is terminated with a
semicolon. For example, the `print` command displays a textual
representation of its argument. For example, suppose the following text
is stored in the file `print.saw`:

````
print 3;
````

Then the command `saw print.saw` will yield output similar to the
following:

````
Loading module Cryptol
Loading file "/Users/atomb/galois/saw-script/doc/print.saw"
3
````

Similarly, the same code can be run from the interactive REPL:

````
sawscript> print 3;
3
````

At the REPL, terminating semicolons can be omitted:

````
sawscript> print 3
3
````

To make common use cases simpler, bare values at the REPL are treated as
if they were arguments to `print`:

````
sawscript> 3
3
````

## Basic Types and Values

All values in SAWScript have types, and these types are determined and
checked before a program runs (that is, SAWScript is statically typed).
The basic types available are similar to those in many other languages.

* The `Int` type represents unbounded mathematical integers. Integer
  constants can be written in decimal notation (e.g., `42`), hexidecimal
  notation (`0x2a`), and binary (`0b00101010`). However, unlike many
  languages, integers in SAWScript are used primarily as constants.
  Arithmetic is usually encoded in Cryptol, as discussed in the next
  section.

* The Boolean type, `Bool`, contains the values `true` and `false`, like
  in many other languages. As with integers, computations on Boolean
  values usually occur in Cryptol.

* Values of any type can be aggregated into tuples. For example, the
  value `(true, 10)` has the type `(Bool, Int)`.

* Values of any type can also be aggregated into records, which are
  exactly like tuples except that their components have names. For
  example, the value `{ b = true, n = 10 }` has the type `{ b : Bool,
  n : Int }`.

* A sequence of values of the same type can be stored in a list. For
  example, the value `[true, false, true]` has the type `[Bool]`.

* Strings of textual characters can be represented in the `String` type.
  For example, the value `"example"` has type `String`.

* The "unit" type, written `()` is essentially a placeholder. It has
  only one value, also written `()`. Values of type `()` essentially
  convey no information. We will show in later sections several cases
  where this is useful.

SAWScript also includes some more specialized types which do not have a
straightforward counterpart in most other languages. These will appear
in later sections.

## Basic Expression Forms

One of the key forms of top-level command in SAWScript is a *binding*,
introduced with the `let` keyword, which gives a name to a value. For
example:

````
sawscript> let x = 5
sawscript> x
5
````

Bindings can have parameters, in which case they define functions. For
instance, the following function takes one parameter and constructs a
list containing that parameter as its single element.

````
sawscript> let f x = [x]
sawscript> f "text"
["text"]
````

Functions themselves are values, and have types. The type of a function
that takes an argument of type `a` and returns a result of type `b` is
`a -> b`. Typically, the types of functions are inferred. As in the
example `f` above. In this case, because `f` only creates a list with
the given argument, and it's possible to create a list of any element
type, `f` can be applied to an argument of any type. We say, therefore,
that it's *polymorphic*. This means we can also apply it to `10`:

````
sawscript> f 10
[10]
````

However, we may want to specify that a function operates at a more
specific type than the most general type possible. In this case, we
could restrict `f` to operate only on `Int` parameters.

````
sawscript> let f (x : Int) = [x]
````

This will work identically to the original `f` on an `Int` parameter:

````
sawscript> f 10
[10]
````

But it will fail for a `String` parameter.

````
sawscript> f "text"

type mismatch: String -> t.0 and Int -> [Int]
 at "_" (REPL)
mismatched type constructors: String and Int
````

Type annotations can be applied to any expression. The notation `(e :
t)` indicates that the expression `e` is expected to have type `t`, and
that it is an error for it to have a different type. Most types in
SAWScript are inferred automatically, but it can sometimes be valuable
for readability to specify them explicitly.

In the text so far, we have used the terms *function* and *command*, and
we take these to mean slightly different things. A function is any value
with a function type (e.g., `Int -> [Int]`). A command is a function in
which the result type is one of a specific set of *parameterized* types,
or types that take other types as parameters. We have seen one of these
so far: the list type, such as the type `[Bool]` indicating lists of
Boolean values. The most important parameterized type is the `TopLevel`
type, indicating a command that can run at the top level. The `print`
command has the type `a -> TopLevel ()`, where the `a` indicates that
its parameter can be of any type and `TopLevel ()` means that it is a
command that runs in the `TopLevel` context and returns a value of type
`()` (that is, no useful information). This is the primary place where
you'll see the `()` type used.

TODO: type variables

TODO: help command

It can sometimes be useful to bind together a sequence of commands in a
unit. This can be accomplished with the `do { ... }` construct. For
example:

````
sawscript> let print_two = do { print "first"; print "second"; }
sawscript> print_two
first
second
````

The bound value, `print_two`, has type `TopLevel ()`, since that is the
type of its last command.

TODO: binding the results of commands, and the distinction between let
and <-

# The Term Type

Perhaps the most important type in SAWScript, and the one most unlike
the built-in types of most other languages, is the `Term` type.
Essentially, a value of type `Term` precisely describes all of the
possible computations performed by some program. And, in particular, if
two `Term` values are *equivalent*, then the programs that they
represent perform equivalent computations. We will say more later about
what exactly it means for two terms to be equivalent, and how to
determine whether two terms are equivalent.

Before we dig into the `Term` type more deeply, it will be useful to
describe the role of the Cryptol language in SAW.

# Cryptol and its Role in SAW

Cyptol is a domain-specific language originally designed for the
high-level specification of cryptographic algorithms. It is general
enough, however, to describe a wider variety of programs, and is
particularly applicable to describing computations that operate on data
of some fixed size.

Because Cryptol is a stand-alone language in addition to being
integrated into SAW, it has its own manual, which you can find here:

    http://cryptol.net/files/ProgrammingCryptol.pdf

SAW includes deep support for Cryptol, and in fact requires the use of
Cryptol for most non-trivial tasks. The primary use of Cryptol is to
construct values of type `Term`. Although `Term` values can be
constructed from various sources, inline Cryptol expressions are the
most direct and convenient way to create them.

Specifically, a Cryptol expression can be placed inside double curly
braces (`{{` and `}}`), resulting in a value of type `Term`. As a very
simple example, there is no built-in integer addition operation in
SAWScript, but there is in Cryptol, and we can use it as follows:

````
sawscript> let t = {{ 0x22 + 0x33 }}
sawscript> print t
85
````

Note, however, that although it printed out in the same way as an `Int`,
`t` actually has type `Term`. We can see how this term is represented
internally, before being evaluated, with the `print_term` function.

````
sawscript> print_term t
Cryptol.ecPlus
  (Prelude.Vec 8 Prelude.Bool)
  (Cryptol.OpsSeq
     (Cryptol.TCNum 8)
     Prelude.Bool
     Cryptol.OpsBit)
  (Prelude.bvNat 8 34)
  (Prelude.bvNat 8 51)
````

For the moment, don't try to understand what this output means. We show
it simply to clarify that `Term` values have their own internal
structure that goes beyond what exists in SAWScript.

A `Term` that represents an integer can be translated into a SAWScript
`Int` using the `eval_int` function, of type `Term -> Int`. This
function will return an `Int` if the `Term` can be represented as one,
and will fail at runtime otherwise.

````
sawscript> print (eval_int t)
85
sawscript> print (eval_int {{ True }})

"eval_int" (<stdin>:1:1):
eval_int: argument is not a finite bitvector
sawscript> print (eval_int {{ [True] }})
1
````

Similarly, values of type `Bit` in Cryptol can be translated into values
of type `Bool` in SAWScript using the `eval_bool` function:

````
sawscript> let b = {{ True }}
sawscript> print_term b
Prelude.True
sawscript> print (eval_bool b)
true
````

In addition to being able to extract integer and Boolean values from
Cryptol expressions, `Term` values can be injected into Cryptol
expressions. When SAWScript evaluates a Cryptol expression between `{{`
and `}}` delimiters, it does so with several extra bindings in scope:

* Any value in scope of SAWScript type `Bool` is visible in Cryptol
  expressions as a value of type `Bit`.

* Any value in scope of SAWScript type `Int` is visible in Cryptol
  expressions as *type variable*. Type variables can be demoted to
  numerica bit vector values using the backtick (`\``) operator.

* Any value in scope of SAWScript type `Term` is visible in Cryptol
  expressions as a value with the Cryptol type corresponding to the
  internal type of the term.

To make these rules more concrete, consider the following examples.

TODO: examples

# Transforming Term Values

## Fresh Symbolic Variables

## Rewriting

## Abstraction

## Other Built-in Transformations

# Proofs About Terms

## Proof Commands

## Rewriting to True

## Other Transformation Tactics

## Finishing Off with Automated Provers

## Offline Proofs

# Analyzing Java Programs

# Analyzing LLVM Programs

# Analyzing Go Programs
