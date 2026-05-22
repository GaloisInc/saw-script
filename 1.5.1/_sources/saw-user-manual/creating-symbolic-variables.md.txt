# Creating Symbolic Variables

The direct extraction process discussed previously introduces
symbolic variables and then abstracts over them, yielding a SAWScript
`Term` that reflects the semantics of the original Java, LLVM, or MIR code.
For simple functions, this is often the most convenient interface. For
more complex code, however, it can be necessary (or more natural) to
specifically introduce fresh variables and indicate what portions of the
program state they correspond to.

- `fresh_symbolic : String -> Type -> TopLevel Term` is responsible for
creating new variables in this context. The first argument is a name
used for pretty-printing of terms and counter-examples. In many cases it
makes sense for this to be the same as the name used within SAWScript,
as in the following:

:::{code-block} sawscript
x <- fresh_symbolic "x" ty;
:::

However, using the same name is not required.

The second argument to `fresh_symbolic` is the type of the fresh
variable. Ultimately, this will be a SAWCore type; however, it is usually
convenient to specify it using Cryptol syntax with the type quoting
brackets `{|` and `|}`. For example, creating a 32-bit integer, as
might be used to represent a Java `int` or an LLVM `i32`, can be done as
follows:

:::{code-block} sawscript
x <- fresh_symbolic "x" {| [32] |};
:::

Although symbolic execution works best on symbolic variables, which are
"unbound" or "free", most of the proof infrastructure within SAW uses
variables that are _bound_ by an enclosing lambda expression. Given a
`Term` with free symbolic variables, we can construct a lambda term that
binds them in several ways.

- `abstract_symbolic : Term -> Term` finds all symbolic variables in the
`Term` and constructs a lambda expression binding each one, in some
order. The result is a function of some number of arguments, one for
each symbolic variable. It is the simplest but least flexible way to
bind symbolic variables.

:::{code-block} console
sawscript> x <- fresh_symbolic "x" {| [8] |}
sawscript> let t = {{ x + x }}
sawscript> print_term t
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8))
      x
      x
sawscript> let f = abstract_symbolic t
sawscript> print_term f
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(x : x@1) ->
      Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8)) x x
:::

If there are multiple symbolic variables in the `Term` passed to
`abstract_symbolic`, the ordering of parameters can be hard to predict.
In some cases (such as when a proof is the immediate next step, and it's
expected to succeed) the order isn't important. In others, it's nice to
have more control over the order.

- `lambda : Term -> Term -> Term` is the building block for controlled
binding. It takes two terms: the one to transform, and the portion of
the term to abstract over. Generally, the first `Term` is one obtained
from `fresh_symbolic` and the second is a `Term` that would be passed to
`abstract_symbolic`.

:::{code-block} console
sawscript> let f = lambda x t
sawscript> print_term f
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(x : x@1) ->
      Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8)) x x
:::

- `lambdas : [Term] -> Term -> Term` allows you to list the order in which
symbolic variables should be bound. Consider, for example, a `Term`
which adds two symbolic variables:

:::{code-block} console
sawscript> x1 <- fresh_symbolic "x1" {| [8] |}
sawscript> x2 <- fresh_symbolic "x2" {| [8] |}
sawscript> let t = {{ x1 + x2 }}
sawscript> print_term t
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8))
      x1
      x2
:::

We can turn `t` into a function that takes `x1` followed by `x2`:

:::{code-block} console
sawscript> let f1 = lambdas [x1, x2] t
sawscript> print_term f1
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(x1 : x@1) ->
      \(x2 : x@1) ->
        Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8)) x1
          x2
:::

Or we can turn `t` into a function that takes `x2` followed by `x1`:

:::{code-block} console
sawscript> let f1 = lambdas [x2, x1] t
sawscript> print_term f1
let { x@1 = Prelude.Vec 8 Prelude.Bool
    }
 in \(x2 : x@1) ->
      \(x1 : x@1) ->
        Cryptol.ecPlus x@1 (Cryptol.PArithSeqBool (Cryptol.TCNum 8)) x1
          x2
:::
