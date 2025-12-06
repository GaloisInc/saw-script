# Using Cryptol in SAWScript

The primary use of Cryptol within SAWScript is to construct values of type
`Term`. Although `Term` values can be constructed from various sources,
inline Cryptol expressions are the most direct and convenient way to create
them.

Specifically, a Cryptol expression can be placed inside double curly
braces (`{{` and `}}`), resulting in a value of type `Term`. As a very
simple example, there is no built-in integer addition operation in
SAWScript. However, we can use Cryptol's built-in integer addition operator
within SAWScript as follows:

:::{code-block} console
sawscript> let t = {{ 0x22 + 0x33 }}
sawscript> print t
85
sawscript> :type t
Term
:::

Although it printed out in the same way as an `Int`, it is important to
note that `t` actually has type `Term`. We can see how this term is
represented internally, before being evaluated, with the `print_term`
function.

:::{code-block} console
sawscript> print_term t
let { x@1 = Prelude.Vec 8 Prelude.Bool
      x@2 = Cryptol.TCNum 8
      x@3 = Cryptol.PLiteralSeqBool x@2
    }
 in Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool x@2)
      (Cryptol.ecNumber (Cryptol.TCNum 34) x@1 x@3)
      (Cryptol.ecNumber (Cryptol.TCNum 51) x@1 x@3)
:::

For the moment, it's not important to understand what this output means.
We show it only to clarify that `Term` values have their own internal
structure that goes beyond what exists in SAWScript. The internal
representation of `Term` values is in a language called SAWCore. The
full semantics of SAWCore are beyond the scope of this manual.

The text constructed by `print_term` can also be accessed
programmatically (instead of printing to the screen) using the
`show_term` function, which returns a `String`. The `show_term` function
is not a command, so it executes directly and does not need `<-` to bind
its result. Therefore, the following will have the same result as the
`print_term` command above:

:::{code-block} console
sawscript> let s = show_term t
sawscript> :type s
String
sawscript> print s
<same as above>
:::

Numbers are printed in decimal notation by default when printing terms,
but the following two commands can change that behavior.

- `set_ascii : Bool -> TopLevel ()`, when passed `true`, makes
subsequent `print_term` or `show_term` commands print sequences of bytes
as ASCII strings (and doesn't affect printing of anything else).

- `set_base : Int -> TopLevel ()` prints all bit vectors in the given
base, which can be between 2 and 36 (inclusive).

A `Term` that represents an integer (any bit vector, as affected by
`set_base`) can be translated into a SAWScript `Int` using the
`eval_int : Term -> Int` function. This function returns an
`Int` if the `Term` can be represented as one, and fails at runtime
otherwise.

:::{code-block} console
sawscript> print (eval_int t)
85
sawscript> print (eval_int {{ True }})

"eval_int" (<stdin>:1:1):
eval_int: argument is not a finite bitvector
sawscript> print (eval_int {{ [True] }})
1
:::

Similarly, values of type `Bit` in Cryptol can be translated into values
of type `Bool` in SAWScript using the `eval_bool : Term -> Bool` function:

:::{code-block} console
sawscript> let b = {{ True }}
sawscript> print_term b
Prelude.True
sawscript> print (eval_bool b)
true
:::

Anything with sequence type in Cryptol can be translated into a list of
`Term` values in SAWScript using the `eval_list : Term -> [Term]` function.

:::{code-block} console
sawscript> let l = {{ [0x01, 0x02, 0x03] }}
sawscript> print_term l
let { x@1 = Prelude.Vec 8 Prelude.Bool
      x@2 = Cryptol.PLiteralSeqBool (Cryptol.TCNum 8)
    }
 in [Cryptol.ecNumber (Cryptol.TCNum 1) x@1 x@2
    ,Cryptol.ecNumber (Cryptol.TCNum 2) x@1 x@2
    ,Cryptol.ecNumber (Cryptol.TCNum 3) x@1 x@2]
sawscript> print (eval_list l)
[Cryptol.ecNumber (Cryptol.TCNum 1) (Prelude.Vec 8 Prelude.Bool)
  (Cryptol.PLiteralSeqBool (Cryptol.TCNum 8))
,Cryptol.ecNumber (Cryptol.TCNum 2) (Prelude.Vec 8 Prelude.Bool)
  (Cryptol.PLiteralSeqBool (Cryptol.TCNum 8))
,Cryptol.ecNumber (Cryptol.TCNum 3) (Prelude.Vec 8 Prelude.Bool)
  (Cryptol.PLiteralSeqBool (Cryptol.TCNum 8))]
:::

Finally, a list of `Term` values in SAWScript can be collapsed into a single
`Term` with sequence type using the `list_term : [Term] -> Term` function,
which is the inverse of `eval_list`.

:::{code-block} console
sawscript> let ts = eval_list l
sawscript> let l = list_term ts
sawscript> print_term l
let { x@1 = Prelude.Vec 8 Prelude.Bool
      x@2 = Cryptol.PLiteralSeqBool (Cryptol.TCNum 8)
    }
 in [Cryptol.ecNumber (Cryptol.TCNum 1) x@1 x@2
    ,Cryptol.ecNumber (Cryptol.TCNum 2) x@1 x@2
    ,Cryptol.ecNumber (Cryptol.TCNum 3) x@1 x@2]
:::

In addition to being able to extract integer and Boolean values from
Cryptol expressions, `Term` values can be injected into Cryptol
expressions. When SAWScript evaluates a Cryptol expression between `{{`
and `}}` delimiters, it does so with several extra bindings in scope:

- Any variable in scope that has SAWScript type `Bool` is visible in
  Cryptol expressions as a value of type `Bit`.

- Any variable in scope that has SAWScript type `Int` is visible in
  Cryptol expressions as a _type variable_. Type variables can be
  demoted to numeric bit vector values using the backtick (`` ` ``)
  operator.

- Any variable in scope that has SAWScript type `Term` is visible in
  Cryptol expressions as a value with the Cryptol type corresponding to
  the internal type of the term. The power of this conversion is that
  the `Term` does not need to have originally been derived from a
  Cryptol expression.

In addition to these rules, bindings created at the Cryptol level,
either from imported files or inside Cryptol quoting brackets, are
visible only to later Cryptol expressions, and not as SAWScript
variables.

To make these rules more concrete, consider the following examples. If
we bind a SAWScript `Int`, we can use it as a Cryptol type variable. If
we create a `Term` variable that internally has function type, we can
apply it to an argument within a Cryptol expression, but not at the
SAWScript level:

:::{code-block} console
sawscript> let n = 8
sawscript> :type n
Int
sawscript> let {{ f (x : [n]) = x + 1 }}
sawscript> :type {{ f }}
Term
sawscript> :type f

<stdin>:1:1-1:2: unbound variable: "f" (<stdin>:1:1-1:2)
sawscript> print {{ f 2 }}
3
:::

If `f` was a binding of a SAWScript variable to a `Term` of function
type, we would get a different error:

:::{code-block} console
sawscript> let f = {{ \(x : [n]) -> x + 1 }}
sawscript> :type {{ f }}
Term
sawscript> :type f
Term
sawscript> print {{ f 2 }}
3
sawscript> print (f 2)

type mismatch: Int -> t.0 and Term
 at "_" (REPL)
 mismatched type constructors: (->) and Term
:::

One subtlety of dealing with `Term`s constructed from Cryptol is that
because the Cryptol expressions themselves are type checked by the
Cryptol type checker, and because they may make use of other `Term`
values already in scope, they are not type checked until the Cryptol
brackets are evaluated. So type errors at the Cryptol level may occur at
runtime from the SAWScript perspective (though they occur before the
Cryptol expressions are run).

So far, we have talked about using Cryptol _value_ expressions. However,
SAWScript can also work with Cryptol _types_. The most direct way to
refer to a Cryptol type is to use type brackets: `{|` and `|}`. Any
Cryptol type written between these brackets becomes a `Type` value in
SAWScript. Some types in Cryptol are _numeric_ (also known as _size_)
types, and correspond to non-negative integers. These can be translated
into SAWScript integers with the `eval_size` function. For example:

:::{code-block} console
sawscript> let {{ type n = 16 }}
sawscript> eval_size {| n |}
16
sawscript> eval_size {| 16 |}
16
:::

For non-numeric types, `eval_size` fails at runtime:

:::{code-block} console
sawscript> eval_size {| [16] |}

"eval_size" (<stdin>:1:1):
eval_size: not a numeric type
:::

In addition to the use of brackets to write Cryptol expressions inline,
several built-in functions can extract `Term` values from Cryptol files
in other ways. The `import` command at the top level imports all
top-level definitions from a Cryptol file or module and places them in scope
within later bracketed expressions. This includes [Cryptol `foreign`
declarations](https://galoisinc.github.io/cryptol/master/FFI.html). If a
[Cryptol implementation of a foreign
function](https://galoisinc.github.io/cryptol/master/FFI.html#cryptol-implementation-of-foreign-functions)
is present, then it will be used as the definition when reasoning about
the function. Otherwise, the function will be imported as an opaque
constant with no definition.

The `cryptol_load` command behaves similarly, but returns a
`CryptolModule` instead. If any `CryptolModule` is in scope, its
contents are available qualified with the name of the `CryptolModule`
variable. A specific definition can be explicitly extracted from a
`CryptolModule` using the `cryptol_extract` command:

- `cryptol_extract : CryptolModule -> String -> TopLevel Term`
