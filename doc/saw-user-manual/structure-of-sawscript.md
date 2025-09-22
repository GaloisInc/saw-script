# Structure of SAWScript

SAWScript is an application-level scripting language used for scripting
proof developments, running proofs, writing specifications that relate
code to Cryptol models, and also applying proof tactics and scripting
individual proofs.
It is not itself either a proof language or a specification language:
proofs themselves are expressed in SAWCore, and for the most part the
models that underlie specifications are written in Cryptol.
(The role of SAWScript in code specifications is to relate program
elements to Cryptol fragments, not to write the specifications
directly.)

SAWScript is a strongly typed language, and a pure functional language,
with monads for sequencing execution.
There are five monads in SAWScript; these are all built in to the
language and more cannot be created.
These monads and their purposes are:
 - `TopLevel`: start proofs, control things, operate SAW
 - `ProofScript`: apply tactics and solve proof goals
 - `LLVMSetup`: assemble specifications for functions imported from LLVM bitcode
 - `JVMSetup`: assemble specifications for functions imported from Java byte code
 - `MIRSetup`: assemble specifications for functions imported via Rust MIR

Each of these essentially provides a different SAWScript environment for the
stated purpose.
The language is the same for each, but the primitive functions in each monad
that one can use are different in each.
(The `LLVMSetup`, `JVMSetup`, and `MIRSetup` environments are very similar to
one another, but some details vary.)

The pure (non-monadic) fragment of SAWScript is very small and has
little practical use; most things one does are written in one or
another of the monads.

## Lexical Structure and Basic Syntax

The syntax of SAWScript is reminiscent of functional languages such as
Cryptol, Haskell and ML.
In particular, functions are applied by writing them next to their
arguments rather than by using parentheses and commas.
Rather than writing `f(x, y)`, write `f x y`.

Comments are written as in C, Java, and Rust (among many other languages).
All text from `//` until the end of a line is ignored:
:::{code-block} sawscript
   let x = 3; // this is a comment
:::
Additionally, all text between `/*` and `*/` is ignored, regardless of
whether the line ends.
Unlike in C, `/* */` comments nest.
:::{code-block} sawscript
   /*
    * This is a comment
    *   /* and so is this */
    */
   let x = 3;
:::

Identifiers begin with a letter and, like Haskell and ML, can contain
letters, digits, underscore, and single-quote.
:::{code-block} sawscript
   let x = 3;
   let x' = 4;
   let x2 = 6;
:::

Integer constants can be prefixed with `0x` and `0X` for hex, `0o`
and `0O` for octal, or `0b` and `0B` for binary.
Otherwise they are read as decimal.
Floating-point constants are not currently supported.
:::{code-block} sawscript
   let x = 0x30; /* 48 */
   let x = 0o30; /* 24 */
   let x = 0b11; /* 3 */
   let x = 0100; /* 100 */
:::

String constants are written in double quotes, and can contain
conventional escape sequences like `\t` and `\n`.
:::{code-block} sawscript
   print "Hello!\nI am a proof agent!";
:::
The forms `\72`, `\o72`, and `\x72` produce the character numbered 72
in decimal, octal, and hex respectively.
Character numbers are Unicode code points.
See [XXX](XXX) for the complete list of escape sequences.

<!-- XXX move this to the reference and update the above reference -->
<!-- XXX check the rendering of the table -->
<!-- XXX there's also a \& that does IDK -->
The full set of escape sequences recognized in string literals is as
follows:

:::{table} Escape sequences for control characters
| Number | By letter | By control-letter | By ASCII name | Notes           |
| ------ | --------- | ----------------- | ------------- | --------------- |
| 0      |           | `\^@`             | `\NUL`        | null            |
| 1      |           | `\^A`             | `\SOH`        |                 |
| 2      |           | `\^B`             | `\STX`        |                 |
| 3      |           | `\^C`             | `\ETX`        |                 |
| 4      |           | `\^D`             | `\EOT`        |                 |
| 5      |           | `\^E`             | `\ENQ`        |                 |
| 6      |           | `\^F`             | `\ACK`        |                 |
| 7      | `\a`      | `\^G`             | `\BEL`        | beep            |
| 8      | `\b`      | `\^H`             | `\BS`         | backspace       |
| 9      | `\t`      | `\^I`             | `\HT`         | tab             |
| 10     | `\n`      | `\^J`             | `\LF`         | newline         |
| 11     | `\v`      | `\^K`             | `\VT`         | vertical tab    |
| 12     | `\f`      | `\^L`             | `\FF`         | form feed       |
| 13     | `\r`      | `\^M`             | `\CR`         | carriage return |
| 14     |           | `\^N`             | `\SO`         |                 |
| 15     |           | `\^O`             | `\SI`         |                 |
| 16     |           | `\^P`             | `\DLE`        |                 |
| 17     |           | `\^Q`             | `\DC1`        |                 |
| 18     |           | `\^R`             | `\DC2`        |                 |
| 19     |           | `\^S`             | `\DC3`        |                 |
| 20     |           | `\^T`             | `\DC4`        |                 |
| 21     |           | `\^U`             | `\NAK`        |                 |
| 22     |           | `\^V`             | `\SYN`        |                 |
| 23     |           | `\^W`             | `\ETB`        |                 |
| 24     |           | `\^X`             | `\CAN`        |                 |
| 25     |           | `\^Y`             | `\EM`         |                 |
| 26     |           | `\^Z`             | `\SUB`        |                 |
| 27     |           | `\^[`             | `\ESC`        | escape          |
| 28     |           | `\^\`             | `\FS`         |                 |
| 29     |           | `\^]`             | `\GS`         |                 |
| 30     |           | `\^^`             | `\RS`         |                 |
| 31     |           | `\^_`             | `\US`         |                 |
| 127    |           |                   | `\DEL`        | delete / rubout |
:::

By the traditional usage of `^` with control characters, one might
expect `\^?` to also produce DEL, but it does not, apparently because
that escape sequence is not supported in Haskell.

:::{table} Other escape sequences
| Sequence | Produces                               |
| -------- | -------------------------------------- |
| `\\`     | literal backslash                      |
| `\"`     | double-quote character                 |
| `\'`     | single-quote character                 |
| `\SP`    | space (character 32)                   |
| `\123`   | character 123 (in decimal)             |
| `\o123`  | character 123 in octal (83 in decimal) |
| `\x123`  | character 123 in hex (291 in decimal)  |
:::

The numeric escape sequences (the last three forms) are processed by first
collecting all legal digits, then converting that to a number and rejecting
numbers that are too large or illegal Unicode.
Thus for example `\o339` produces an escape (character 27) followed by '9',
because 9 isn't a legal octal digit.
Conversely, `\xaaaaaaaaa` will fail, even though there's a possible
interpretation of it as a valid code point followed by more `a`s.

Text enclosed in double curly braces (`{{ }}`) is treated as Cryptol
code (in particular, a Cryptol expression) and parsed by the Cryptol
parser.
Text enclosed in curly braces and bars (`{| |}`) is parsed as a Cryptol
type.
Cryptol types are expressions at the SAWScript level, as discussed below.
:::{code-block} sawscript
   let xs = {{ [1, 2, 3] }};
   let t = {| Integer |};
:::

The following identifiers are reserved words:

:::{list-table}
* - `and`
  - `do`
  - `hiding`
  - `import`
  - `let`
  - `submodule`
  - `typedef`
* - `as`
  - `else`
  - `if`
  - `in`
  - `rec`
  - `then`
  - ` `
:::

The following identifiers for built-in types are also currently
treated as reserved words.
This may change in the future, as handling them as reserved words is
neither necessary nor particularly desirable.

:::{list-table}
* - `AIG`
  - `CrucibleSetup`
  - `JavaSetup`
  - `MIRSpec`
  - `TopLevel`
* - `Bool`
  - `Int`
  - `LLVMSetup`
  - `ProofScript`
  - `Type`
* - `CFG`
  - `JVMMethodSpec`
  - `LLVMSpec`
  - `String`
  -
* - `CrucibleMethodSpec`
  - `JVMSpec`
  - `MIRSetup`
  - `Term`
  -
:::

## Types

SAWScript is strongly typed, as mentioned above.
The following basic types are available:

- `Bool` (booleans; values are spelled `true` and `false`)
- `Int` (unbounded integers)
- `String` (Unicode strings)

There are also the following derived types:

- Tuples.
  Tuple types are written as tuples of types, that is, a comma-separated
  list of types in parentheses.
  An empty pair of parentheses gives the unit type.
  There are no monoples (tuples of arity 1).
- Lists.
  List types are written with a type name in square brackets: `[Int]` is a
  list of integers.
- Records.
  Records are written with curly braces and a comma-separated list of
  field names and type signatures set off with colons: `{ name: String, length: Int }`.
  Record types are purely structural, that is, all record types with the
  same fields of the same types are the same type.
- Functions.
  Function types are written with a right-arrow `->`.
  Functions are curried, so a function of two arguments and a function
  of one argument that returns a function of one argument are the same
  type.

As already mentioned there are five monad types:

- `TopLevel` (the type of generic SAW actions)
- `ProofScript` (the type of proof tactic actions)
- `LLVMSetup` (the type of actions producing LLVM speciications)
- `JVMSetup` (the type of actions producing JVM speciications)
- `MIRSetup` (the type of actions producing MIR speciications)

Monad types have kind `* -> *` (meaning they take an argument) so for
example the type `ProofScript Int` is a computation in the ProofScript
monad that produces an integer when run.

<!-- XXX there's an issue number for this -->
Currently, owing to limitations in the parser,
writing the name of a monad type without an argument will cause a
parse error rather than a type or kinding error.

### Other Built-In Types

There are numerous further built-in types used for various verification
tasks.

<!-- XXX at least some of this should be shoved over to the reference -->

Cryptol-related types:

- `Term` (the type of Cryptol expressions)
- `Type` (the type of Cryptol values)
- `CryptolModule` (a handle for a Cryptol module; see [XXX](XXX imports) below)

Proof-related types:

- `SatResult` (the result produced by the `sat` operation)
- `ProofResult` (the result produced by the `proof` operation)
- `Refnset` (a refinement set; see [XXX](XXX))
- `Simpset` (a simplification set; see [XXX](XXX))
- `Theorem` (a proved theorem)
- `Ghost` (a piece of ghost state used during verification)

Types related to LLVM verification:

- `LLVMModule` (a handle for a loaded module of LLVM bitcode)
- `LLVMType` (the type of LLVM-level types)
- `SetupValue` (the type of LLVM-level values)
- `LLVMSpec` (a proved LLVM specification)
- `CrucibleMethodSpec` (an obsolete alternate name for `LLVMSpec`)

See [XXX](XXX).

Types related to JVM verification:

- `JavaClass` (a handle for a loaded Java byte code class)
- `JavaType` (the type of Java-level types)
- `JVMValue` (the type of Java-level values)
- `JVMSpec` (a proved JVM specification)

See [XXX](XXX).

Types related to MIR verification:

- `MIRModule` (a handle for a loaded module of MIR code)
- `MIRType` (the type of MIR-level types)
- `MIRAdt` (an additional type for MIR-level algebraic data types)
- `MIRValue` (the type of MIR-level values)
- `MIRSpec` (a proved MIR specification)

See [XXX](XXX).

Types related to Yosys verification:

- `YosysSequential` (a handle for a loaded Yosys sequential HDL module)
- `YosysTheorem` (a proved Yosys specification)

Other builtin types:

- `AIG` (an and-inverter graph; see [XXX](XXX))
- `CFG` (a control-flow graph; see [XXX](XXX))
- `FunctionProfile` (a type used by certain analysis operations; see [XXX](XXX))
- `ModuleSkeleton` (a type used by the LLVM skeleton feature; see [XXX](XXX))
- `FunctionSkeleton` (a type used by the LLVM skeleton feature; see [XXX](XXX))
- `SkeletonState` (a type used by the LLVM skeleton feature; see [XXX](XXX))
- `HeapsterEnv` (a type used by Heapster; see [XXX](XXX))
- `BisimTheorem` (a type used by the bisimulation prover; see [XXX](XXX))

### Type Inference

SAWScript supports Hindley-Milner style type inference, so it is
rarely necessary to provide explicit type annotations.

Some exceptions exist:

 - Record inference is not supported, and functions are not row-polymorphic.
   Use type signatures for function arguments of record type.

 - Similarly, tuple arity inference is not supported.
   Use type signatures for function arguments of tuple type that are
   accessed via tuple field selectors.
   (See below).


## Statements and Expressions

Like most programming languages, SAWScript is made up of statements
and expressions.
(There are also declarations, which are syntactically statements.)
Expressions produce a value; statements do not.

The syntactic top level of a SAWScript script is a sequence of
statements, each followed by a semicolon.
These are executed in order.
Do-blocks, a form of expression introduced below, also consist of
sequences of statements followed by semicolons.
These are executed in order when the block itself is executed.
A statement can be either a typedef, a let-binding, a monad-bind, or an import.

Typedefs consist of the keyword `typedef`, an identifier, an equals sign `=`,
and a type name.
These create aliases for existing types.
For example, to make `Foo` another name for the `Int` type:
:::{code-block} sawscript
typedef Foo = Int;
:::

The statement form of let-binding consists of the keyword `let`, an
identifier, optionally a colon and a type name, and then an equal sign
`=` and an expression.
The expression is evaluated, purely (not monadically), and the
resulting value is bound as a new variable.
At the syntactic top leel the resulting variable is global and is accessible
everywhere.
Within a do-block the scope of the variable extends to the end of that do-block.
For example, `let x = 3;` binds `x` to 3, and `let x : String = 3;` produces a
type error.

If more than one identifier is given, the second and subsequent identifiers are
treated as the names of parameters and the result is a function declaration.
The expression is not evaluated until an argument is applied for each parameter.
Parameter names can be given their own type signatures by enclosing the name,
a colon, and the type name in parentheses.
For example:
:::{code-block} sawscript
let intPair (x: Int) (y: Int) = (x, y);
:::

Recursive functions can be written using the keyword `rec` in place of `let`.
Groups of mutually recursive functions can be written using `rec` for the
first function, and then `and` for each successive function, and then finally
a terminating semicolon.

Values of tuple type can be unpacked by writing a tuple pattern (zero
or more variable names or nested tuple patterns) instead of a plain
identifier.
You can explicitly ignore / throw away a value by let-binding it to
the reserved variable name `_`.

It is legal (but useless) to write a function and call it `_`.
It is not legal to write a function that uses a tuple pattern in place
of its name.

Binding a variable name that already exists will, in general, create a
new variable for the new value; the old value is left alone and
references to it is unchanged.
There is an exception to this: values bound at the syntactic top level
are updated when rebound, as if they had been assigned to.
This is a bug and the behavior will be changed in a future release.
See [Issue XXX](XXX).

One can also write `let {{ ... }};`, in which the double-braces can
contain not just an expression but any Cryptol declaration or
let-binding.
This is a convenient way to insert Cryptol type declarations; it also
allows using Cryptol elim forms that cannot readly be expressed directly in
SAWScript.

### Monad Bind

Monad bind is akin to let-binding, except that it requires an expression
of monad type.
The syntax is a variable name, a left arrow `<-`, and an expression.
The expression is first evaluated purely; then, roughly speaking, the
resulting monadic action is executed in its monad, producing a value
which is stored in the variable name.

Precisely speaking, the monad action is bound into the chain of
actions associated with the current do-block (the syntactic top level
being functionally an arbitrary long do-block) and the actions do not
actually _happen_ until that block, and the block it is bound into,
and so forth, and eventually the actions at the syntactic top level,
are all actually executed by the SAWScript interpreter.

If you are not familiar with the use of monads to sequence actions and
carry state around, we recommend you seek out one of the many
explanations available online.

Note however that SAWScript is unlike Haskell in that it executes
eagerly: expressions are evaluated when they are encountered, as in
conventional languages, rather than only when their values are used
somewhere.
Only the execution of monadic actions is delayed.

Monad bind can also use `_` or tuple patterns on the left hand side.
Also, leaving the variable name and the arrow off is entirely is
equivalent to using `_`; that is, `e;` is the same as `_ <- e;`.

The scopes of monad-bound variables are the same as the scopes of
let-bound variables: they go out of scope at the end of the current
do-block, and are global at the syntactic top level.

### Imports

Import statements import Cryptol code.
(To bring in more SAWScript code instead, use `include`.
See [XXX](XXX).)

An import statement begins with the keyword `import` followed by a
module name.
(This can be the file name in double quotes, typically including
the `.cry` suffix.
It can also be an unquoted Cryptol module name, with qualifiers
as needed.)

The module name may be followed with `as` and another module name; this
performs a `qualified import` where the definitions in the module are
accessible using the given alternate name as a prefix.
(Without this, they are imported directly into the current Cryptol
namespace, much as in ordinary Cryptol code.)
For example, if `Foo.cry` contains a definition `Bar`, after
`import "Foo.cry" as Foo;` that definition is accessible as `Foo::Bar`.
After just `import "Foo.cry";` it is accessible unqualified as `Bar`.

Any qualifier name may then be followed by a comma-separated list of
names, in parentheses; only these definitions are imported and all others
are ignored.
Alternatively, if the parenthesized list is preceded by the keyword
`hiding`, the named definitions are the ones ignored and the rest are
imported.

<!--
XXX: there are some other bits to put here, e.g. the _ business, and we
XXX: need a discussion of submodules and functors and interfaces and
XXX: whatnot.
-->

An alternative way to import Cryptol modules is to use the
`cryptol_load` built-in action, which returns a handle of type
`CryptolModule`.
This works the same as a qualified import: after
`Foo <- cryptol_load "Foo.cry";` one can refer to definitions in the
module using `Foo` as a qualifier (e.g. `Foo::Bar`).
One can also look up definitions explicitly using the `cryptol_extract`
builtin: `bar <- cryptol_extract Foo "Bar";`.

### Expressions

Base expressions include constants (integer constants, string constants,
the unit value `()`, and the empty list `[]`), Cryptol expressions in double
curly braces, Cryptol types enclosed in `{| |}`, variable lookups,
and subexpressions in parentheses.

Comma-separated lists of two or more expressions in parentheses are
tuple literals and produce tuple values.
List literals are comma-separated expressions enclosed in square
brackets `[]`.
Record literals are comma-separated lists in single braces `{ }`, where
each field is assigned with a field name, an equal sign `=`, and a
subexpression.
:::{code-block} sawscript
let data = {
   name = "John Smith",
   address = "55 Elm St.",
   city = "Portland",
   state = "Oregon",
   phone = "555-1234"
};
:::

An expression followed by a dot and an identifier looks up the
so-named field in a record value: `data.phone`.
An expression followed by a dot and an integer constant looks up the
nth field of a tuple value.

Juxtaposition of expressions does function application, like in Haskell
and ML: `f x` applies `x` to `f`.

There are four kinds of compound expressions:  let-bindings, lambdas,
ifs, and do-blocks.

The expression forms of let-binding are the same as the statement
forms (they can be single values, functions, recursive systems, have
tuple patterns, etc.) except that instead of having the form
`let x = e;` they have the form `let x = e1 in e2`.
The `e2` is another expression, which is evaluated after the
value for `x` is computed, and the scope of `x` is limited to that
expression.

The syntax `\` followed by a parameter list (with the same syntax as
described for functions above), a right arrow, and a subexpression
forms a lambda: the expression has function type and takes one or more
arguments.
When an argument value for each parameter has been applied, the
expression on the right hand side (called the _body_) is evaluated.
Lambdas are basically in-place function definitions.
For example:
:::{code-block} sawscript
   for [1, 2, 3] (\x -> print x);
:::

Functions let-bound with function syntax and with lambda syntax are
equivalent:
:::{code-block} sawscript
let f x = (0, x);
let g = \x -> (0, x);
:::

If-expressions have the syntax `if e1 then e2 else e3`; the first
(or _control_) expression `e1`, which must be of boolean type, is
evaluated.
If the result is true, `e2` is then evaluated; otherwise, `e3` is
evaluated.
The other expression is ignored.

Do-blocks are introduced by the keyword `do`, and consist of that
keyword followed by a list of statements surrounded by braces.
A do-block is an expression of monadic type, and is roughly comparable
to a lambda expression; much as a lambda does not evaluate until all
arguments are applied, a do-block does not evaluate until the monadic
context is applied.
Thus during pure evaluation do-blocks do not execute.

The last statement in a do-block is restricted to the expression-only
form.
It cannot bind a value to a variable; rather, the value it produces is
the result value of the whole do-block.

(This will often, but not always, be the `return` combinator that
just produces a value without executing anything.)

### Language-Level Builtins

A number of things that are written with syntax in typical languages
are done with builtin functions in SAWScript.
These can be executed as statements where needed.

These include:

 - `include` takes a string and loads and executes a file of SAWScript
   code.
   The code is run in the current context and scope; e.g. it can be
   inside a function or do-block.
   Beware that as of this writing executing things at the syntactic
   top level (e.g. the syntactic top level of an included file) from
   inside a nested context can have odd effects.
   See for example [issue XXX](XXX).
   Note the terminology: `import` is for bringing in Cryptol,
   `include` is for bringing in more SAWScript.

 - `for` takes a list and a monadic action of type `a -> m b`,
   runs the action on each element of the list, and returns a list
   of the results.

 - `caseSatResult` and `caseProofResult` take a `SatResult` or `ProofResult`
   value (respectively) and monadic actions for each possibility,
   and run the action corresponding to the case they find in the result
   argument.
   (This is a workaround for not having a `match` or `case` expression.)

 - `undefined` is a "pure" value that crashes if it is reached, much like
   `undefined` in Haskell.
   It is much like throwing an exception.

 - `fail` is much like `undefined` but is an action in the `TopLevel` monad
    and takes a user-supplied string to print.
   It is also much like throwing an exception.

 - `fails` takes a monadic action and expects it to fail, catching and
    reporting the resulting failure, much like a `try`/`catch` construction.
    As of this writing it does not work reliably;
    see [issue #2424](https://github.com/GaloisInc/saw-script/issues/2424).


## The SAWScript REPL

The most common way to run SAWScript is from a file; however, the
`saw` executable also offers an interactive read-eval-print loop
("REPL") for experimental and debugging use.

The REPL prints a `sawscript>` prompt.
At this prompt one can enter a SAWScript statement, and the SAWScript
interpreter will execute it.
The final semicolon may be left off.
If this produces a value other than `()`, the interpreter will print
the value.

Currently the value must be of type `TopLevel a` for some type `a`.
To evaluate and print a pure expression, use the `return` combinator:
`return (str_concat "abc" "def")` prints `"abcdef"`.
The inability to also handle pure expressions is a bug (or more
accurately, a temporary limitation arising from correcting issues in
the SAWScript interpreter's internals) and will be corrected in a
future release.
See [issue XXX](XXX).

It is also possible to run the REPL in the ProofScript context by
using the `proof_subshell` builtin.
This is an advanced topic; see [XXX](XXX).

The REPL also accepts some REPL-level commands that begin with `:`.
The most immediately useful of these is `:type` or `:t`, which prints
the type of a SAWScript expression.
(For example, `:t 3` prints `Int`.)
The `:h` or `:help` command by itself lists the REPL commands, and if
given the name of a SAWScript value or function, prints its
documentation.

The `:search` command takes one or more type names (separated by
spaces; where necessary use parentheses) and searches the current
variable environment for values that mention all these types.

For example, `:search String -> String` finds the `str_concat`
function mentioned above.

See [the REPL reference](#repl-reference) for further details.


<!--
------------------------------------------------------------
XXX divider of where we've been
-->
# Structure of SAWScript (Previous Version)


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


<!--
------------------------------------------------------------
XXX stuff I wrote that ended up not belonging here; move it
-->
## Some other commands

 - `exec` takes a program name (as a string), an argument list (a
   list of strings) and text to provide on standard input (another
   string), and runs the program.
   The result value is the standard output generated by the program.

 - `show` prints any value to a string, like the function of the same name
   in Haskell.

