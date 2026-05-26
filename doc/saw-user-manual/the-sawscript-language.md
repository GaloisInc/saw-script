(sawscript)=
# The SAWScript Language

SAWScript is an application-level scripting language used for scripting
proof developments, running proofs, assembling specifications that relate
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

SAWScript is normally run from files, and a file consists of a series
of statements executed top-to-bottom; however, a REPL is also provided that
executes one statement at a time interactively.

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
<!--
See [the SAWScript reference manual](#...) for the complete list of
escape sequences.
-->

<!-- XXX move this to the reference and uncomment the above reference -->
<!-- XXX check the rendering of the table -->
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
Digits immediately after a numeric escape can be separated from it
by using the empty escape sequence `\&`.

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

<!--
   Note that the list-table syntax used here creates an NxM table (not
   a nested bullet list) and also requires that there be exactly M
   second-level bullets in each top-level bullet.
   Hence the blank entries.

   It also renders left-to-right then top-to-bottom, so if you want a
   table in normal order that reads top-to-bottom first you need to
   transpose it.
   This is why the ordering is strange.

   Look at the PDF output when editing it.
-->

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
  - ` `
* - `CrucibleMethodSpec`
  - `JVMSpec`
  - `MIRSetup`
  - `Term`
  - ` `
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
  (The unit type has one value, also written `()`; a value of type `()`
  contains no information.
  It is like `void` in C and Java.)
  There are no monoples (tuples of arity 1).
- Lists.
  List types are written with a type name in square brackets: `[Int]` is a
  list of integers.
  Lists must be homogeneous; there is only one element type for the whole list.
- Records.
  Record types are written with curly braces and a comma-separated list of
  field names and type signatures set off with colons:
  `{ name: String, length: Int }`.
  Record types are purely structural, that is, all record types with the
  same fields of the same types are the same type.
  (Note that record _values_ are written with equal signs in place of the
  colons.)
- Functions.
  Function types are written with a right-arrow `->`.
  Functions are curried, so a function of two arguments and a function
  of one argument that returns a function of one argument are the same
  type, and function types with multiple arguments have multiple arrows.

As already mentioned there are five monad types:

- `TopLevel` (the type of generic SAW actions)
- `ProofScript` (the type of proof tactic actions)
- `LLVMSetup` (the type of actions producing LLVM specifications)
- `JVMSetup` (the type of actions producing JVM specifications)
- `MIRSetup` (the type of actions producing MIR specifications)

Monad types take an argument; this is the type the monad yields
when it's run.
For example, the type `ProofScript Int` is a computation in the
ProofScript monad that produces an integer when run.
(In type systems jargon, monads have kind `* -> *`.)

### Other Built-In Types

There are numerous further built-in types used for various verification
tasks.

<!-- XXX at least some of this should be shoved over to the reference -->

Cryptol-related types:

- `Term` (the type of Cryptol expressions and SAWCore value terms)
- `Type` (the type of Cryptol values and SAWCore type terms)
- `CryptolModule` (a handle for a Cryptol module; see [Imports](#imports) below)

Proof-related types:

- `SatResult` (the result produced by the `sat` operation)
- `ProofResult` (the result produced by the `prove` operation)
- `Simpset` (a simplification set; see [Rewriting](#rewriting))
- `Theorem` (a proved theorem)
- `Ghost` (a piece of ghost state used during verification)

Types related to LLVM verification:

- `LLVMModule` (a handle for a loaded module of LLVM bitcode)
- `LLVMType` (the type of LLVM-level types)
- `LLVMValue` (the type of LLVM-level values)
- `LLVMSpec` (a proved LLVM specification)
- `CrucibleMethodSpec` (an obsolete alternate name for `LLVMSpec`)

See [LLVM Types](#llvm-types).

Types related to JVM verification:

- `JavaClass` (a handle for a loaded Java byte code class)
- `JavaType` (the type of Java-level types)
- `JVMValue` (the type of Java-level values)
- `JVMSpec` (a proved JVM specification)

See [JVM Types](#jvm-types).

Types related to MIR verification:

- `MIRModule` (a handle for a loaded module of MIR code)
- `MIRType` (the type of MIR-level types)
- `MIRAdt` (an additional type for MIR-level algebraic data types)
- `MIRValue` (the type of MIR-level values)
- `MIRSpec` (a proved MIR specification)

See [MIR Types](#mir-types).

Types related to Yosys verification:

- `YosysSequential` (a handle for a loaded Yosys sequential HDL module)
- `YosysTheorem` (a proved Yosys specification)

Other builtin types:

- `AIG` (an and-inverter graph; see [AIG Values and Proofs](aig-values-and-proofs))
- `CFG` (a control-flow graph)
- `FunctionProfile` (a type used by certain analysis operations)
- `ModuleSkeleton` (a type used by the LLVM skeleton feature)
- `FunctionSkeleton` (a type used by the LLVM skeleton feature)
- `SkeletonState` (a type used by the LLVM skeleton feature)
- `BisimTheorem` (a type used by the bisimulation prover; see [Bisimulaton Prover](#bisimulation-prover))

<!--
   XXX: the functionality associated with the CFG, FunctionProfile, and Skeleton
   types all seems to be entirely undocumented.
   That should get fixed and there should be references above.
-->

### Type Inference

SAWScript supports Hindley-Milner style type inference, including
parametric polymorphism, so it is rarely necessary to provide explicit
type annotations.

Some exceptions exist:

 - Record inference is not supported, and functions are not row-polymorphic.
   Use type signatures for function arguments of record type.

 - Similarly, tuple arity inference is not supported.
   Use type signatures for function arguments of tuple type that are
   accessed via tuple field selectors.
   (See below).

The concrete syntax `{a}` is used for forall-quantification of type
schemes, following Cryptol.

## Statements

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
At the syntactic top level the resulting variable is global and is accessible
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
or more variable names or nested tuple patterns in parentheses)
instead of a plain identifier.
You can explicitly ignore / throw away a value by let-binding it to
the reserved variable name `_`.

It is legal (but useless) to write a function and call it `_`.
It is not legal to write a function that uses a tuple pattern in place
of its name.

Binding a variable name that already exists will, in general, create a
new variable for the new value; the old value is left alone and
references to it are unchanged.

There is an exception to this: global variables at the syntactic top
level can be bound with the special variant syntax
`let rebindable ...`.
These variables can then be updated by a subsequent `let rebindable`;
in effect they are mutable globals.
Updates must be with the same type, which must be monomorphic.
See [Issue 1646](https://github.com/GaloisInc/saw-script/issues/1646)
for further discussion and the history of this (somewhat dubious)
feature.
Note that `rec rebindable` is not permitted, and variables bound with
`<-` cannot be rebindable either.
Rebinding a `rebindable` variable with a _non_-rebindable definition
masks it with a new immutable version, but does _not_ update it.

One can also write `let {{ ... }};`, in which the double-braces can
contain not just an expression but any Cryptol declaration or
let-binding.
This is a convenient way to insert Cryptol type declarations; it also
allows using Cryptol binding patterns that cannot readly be expressed
directly in SAWScript.

(monad-bind)=
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
Also, leaving the variable name and the arrow off is entirely
equivalent to using `_`; that is, `e;` is the same as `_ <- e;`.

The scopes of monad-bound variables are the same as the scopes of
let-bound variables: they go out of scope at the end of the current
do-block, and are global at the syntactic top level.

(imports)=
### Imports

Import statements import Cryptol code.
(To bring in more SAWScript code instead, use `include` or `include_once`.
See the next section.)

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

### Includes

Additional SAWScript code can be loaded with the `include` and
`include_once` statements.

`include` takes a string constant and loads and executes a file of
SAWScript code.
The code is run in the current context and scope; e.g. it can be
inside a function or do-block.
Beware that as of this writing executing things at the syntactic
top level (e.g. the syntactic top level of an included file) from
inside a nested context can have odd effects.
<!-- See for example [issue ...](...).
   ... I can't find an issue. I think the worst effects were fixed
   when the interpreter's environments got fixed up, but I'm also
   not yet willing to remove the warning as there's plenty of
   strange things left.
-->
Note the terminology: `import` is for bringing in Cryptol,
`include` is for bringing in more SAWScript.

`include_once` is like `include`, except that if the same file has
already been included it does nothing.
(The file is the "same" based on the filename.
The test does not chase symlinks or inspect OS-level markers for
file identity.)

SAWScript does not have a module system and there is no more
structured way to load SAWScript code.

## Expressions

Base expressions include constants (integer constants, string constants,
the unit value `()`, and the empty list `[]`), Cryptol expressions in double
curly braces, Cryptol types enclosed in `{| |}`, variable lookups including
names of builtins, and subexpressions in parentheses.

Comma-separated lists of two or more expressions in parentheses are
tuple literals and produce tuple values.
List literals are comma-separated expressions enclosed in square
brackets `[]`.
Record literals are comma-separated lists in single braces `{ }`, where
each field is assigned with a field name, an equal sign `=`, and a
subexpression.
(As mentioned above, record _types_ have a similar syntax but use colons
instead of equal signs.)
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
Tuple indexes are zero-based.

Juxtaposition of expressions does function application, like in Haskell
and ML: `f x` applies the function `f` to an argument `x`.

There are no infix operators.
Arithmetic (and computation on boolean values) is done in Cryptol blocks.

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
    It can only catch failures that occur within the monadic action;
    in particular to catch the failure of a pure function, it must be
    enclosed in a do-block when passed to `fails`.
    Otherwise the failure happens evaluating the function before `fails`
    starts.
    See [issue #2424](https://github.com/GaloisInc/saw-script/issues/2424)
    for further discussion.

### Library-Level Builtins

There is no SAWScript prelude as such, just a collection of builtins that
resemble a standard library.
Here are some of the functions available:

#### String Functions

- `show : {a} a -> String` computes the textual representation of its
argument in the same way as `print`, but instead of displaying the value
it returns it as a `String` value for later use in the program. This can
be useful for constructing more detailed messages later.

- `str_concat : String -> String -> String` concatenates two `String`
values, and can also be useful with `show`.

#### List Functions

- `concat : {a} [a] -> [a] -> [a]` takes two lists and returns the
  concatenation of the two.
  Note that this is more usually called `append`; the function
  more usually called `concat` is called `XXX` in SAWScript.

- `head : {a} [a] -> a` returns the first element of a list.

- `tail : {a} [a] -> [a]` returns everything except the first element.

- `length : {a} [a] -> Int` counts the number of elements in a list.

- `null : {a} [a] -> Bool` indicates whether a list is empty (has zero
elements).

- `nth : {a} [a] -> Int -> a` returns the element at the given position,
with `nth l 0` being equivalent to `head l`.

Calling `head` or `tail` on an empty list, or asking `nth` for an element
past the end of the list, will produce a runtime error.

#### Timing Functions

- `time : {a} TopLevel a -> TopLevel a` runs any other `TopLevel`
command and prints out the time it took to execute.

- `with_time : {a} TopLevel a -> TopLevel (Int, a)` returns both the
original result of the timed command and the time taken to execute it
(in milliseconds), without printing anything in the process.

- `timeout : {a} Int -> TopLevel a -> TopLevel a` takes a timeout
  in milliseconds and an action to run.
  If the action takes longer, it is stopped and `timeout` fails.

- `timeout_handle : {a} Int -> TopLevel a -> TopLevel a -> TopLevel a` is
  like `timeout` but takes an additional action that is run if the
  operation times out.

The `timeout` and `timeout_handle` builtins, like the `fails` builtin,
can only handle timeouts in monadic actions.
If you need a timeout for a pure function, wrap it in a do-block.

#### System Functions

- `get_opt` _`n`_ returns the current script's command-line argument
  _`n`_.
  Argument 0 is the script name; higher indices represent later
  arguments.

- `get_nopts` `()` returns the number of arguments given to the
  current script.
  As in the shell, the arguments to the script follow the script name
  on `saw`'s own command line.

- `get_env` _`name`_ (where _`name`_ is a `String`) returns the value
  of an environment variable in SAW's process environment.

- `read_bytes` _`filename`_, whose return type is `TopLevel` `Term`,
  reads a file, treating it as
  binary, and returns the contents as a list of bytes.
  The underlying type of the resulting `Term` is `[`_`n`_`][8]`
  for some _`n`_ corresponding to the length of the file.

- `exec` _`program`_ _`args`_ _`input-text`_ is a `TopLevel`
  function that runs an external program.
  The _`input-text`_ is sent as the program's standard input.
  The return value is the program's resulting standard output, as a
  `String`.
  Its standard error is not captured and will print to the terminal.
  The list of argument strings _`args`_ should include a first entry
  to be the program's `argv[0]`.

- `exit` _`code`_, whose full type is `Int -> TopLevel ()`,
  stops execution of the current script and
  returns the exit code _`code`_ to the operating system.

#### Verification Builtins

There are many other builtins for doing various kinds of verification
tasks.
These have been introduced already, or will be introduced later,
elsewhere in the manual.

See the [SAWScript Commands Reference](#commands-reference) in the
reference manual for the comprehensive list.
You can also use `:search` in the REPL to find them by type.

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

The value must either be of type `TopLevel a` for some type `a`, or
pure (not in any monad).

It is also possible to run the REPL in the ProofScript context by
using the `proof_subshell` builtin.
This is an advanced topic; see [Interactive Proofs](interactive-proofs).

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

I don't think we need this example any more (there are other simple
examples earlier) but I don't want to just toss it out yet, so I'm
going to leave it here commented out.

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

-->
