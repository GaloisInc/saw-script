# Overview

This directory contains a backend for `saw` for translating Cryptol
modules into Isabelle/Isar theory files. The resulting theories
depend on the included supporting libraries included in the
`isabelle/theories` subdirectory.

# Preamble

The translation from Cryptol into Isabelle is intended to yield a semantically-equivalent collection of
Isabelle definitions, while preserving the structure of the original Cryptol as much as possible.
The expression language and type system of Cryptol is similar enough to Isabelle to allow this
translation to be very shallow and relatively straightforward, with a few notable exceptions.

While this allows the translated theories to look fairly similar to the source Cryptol, they
should still be considered a best-effort interpretation, and treated with the same skepticism as if they
had been written manually.


# Quickstart

The translator is available as an independent executable, which is built
with the other SAW binaries via `build.sh` at the toplevel of this repository.
Similar to `saw` or `cryptol`, it assumes that an appropriate `z3` executable
is available in the current PATH.

At least three arguments are required: the source `.cry` file for a Cryptol module,
a destination directory, and a flag to indicate which modules should be translated.

```
./bin/cryptol-to-isabelle ./examples/ecdsa/cryptol-spec/bv.cry -d /tmp/ --all-modules
```

This will translate all Cryptol definitions from `bv.cry` into corresponding Isabelle
definitions in `/tmp/bv.thy`. The next section outlines how to install the supporting
Cryptol theories in order to load this theory in Isabelle/jEdit.


# Support Library for Isabelle

The toplevel supporting theory is `isabelle/theories/Cryptol.thy`, which provides
syntax extensions and additional Isar commands required for parsing translated Cryptol modules.
This library is compatible with `Isabelle2025-2` and depends on a corresponding version of
the [afp](https://www.isa-afp.org/download/). Add this as a component to Isabelle by
first extracting the afp archive and then executing the following command:

```
isabelle components -u /path/to/afp/thys
```

Then add the Cryptol library as a component:

```
isabelle components -u /path/to/saw/saw-core-isabelle/isabelle
```

Then the Cryptol session can be built as an image with the command:


```
isabelle build -bv Cryptol
```

Once this finishes, run Isabelle/jEdit with the `Cryptol` logic session:

```
isabelle jedit -l Cryptol
```

This will open the jEdit IDE with the `Cryptol` supporting theories loaded.
Any translated theory files will import the `Cryptol.Cryptol` theory, which will
now be in scope if opened in this jEdit session.

# Cryptol to Isabelle

The translation from Cryptol to Isabelle syntax is a straightforward conversion
from type-checked Cryptol expressions to structurally-equivalent Isabelle expressions.
These resulting expressions require the syntax extensions from the supporting library
in order to parse correctly.

For example, the Cryptol function from `bv.cry` is defined as:

```
uext : {a, b} (fin a, fin b) => [a] -> [a+b]
uext(x) = zero # x
```

Which Cryptol parses and type-checks into:

```
bv::uext : {a, b} (fin a, fin b) => [a] -> [a + b]
bv::uext =
  \{a, b} (fin a, fin b) (x : [a]) ->
    (Cryptol::#) b a Bit <> (Cryptol::zero [b] <>) x
```

This is the input to the translator, which produces the following Isabelle definition:

```
cryptol_definition uext :: "{'a,'b} ((fin 'a,fin 'b) =?> ((['a]) ⇒ (['a + 'b])))" where
"uext x ≡ (zero`{['b]}) #`{'b,'a,Bit} x"
```

This definition can only be parsed with the syntax extensions from the provided Cryptol
library. A large portion of the extensions are only used for parsing, which define
the mapping from Cryptol primitives to Isabelle definitions (e.g. converting `#` into `append_seq`).
The pretty-printed definition still contains some custom syntax:

```
uext :: {'a,'b} ['a] ⇒ ['a + 'b]
uext uu uv x ≡ (('a topT,'b topT) ⇒ append_seq 0 x : ['a + 'b])
```

But this often disappears after simplification:

```
uext uu uv x ≡ append_seq 0 x
```

# Cryptol library for Isabelle

The straightforward conversion from Cryptol to Isabelle syntax effectively
pushes most of the translation complexity into the supporting theories.
These theories provide the mapping from the generated Cryptol-like syntax in Isabelle
into formal definitions/semantics. This is a brief overview of the core theories:

* Cryptol.thy
  * toplevel import for all translated theories

* Cryptol_Syntax.thy
  * syntax and abbreviations for Cryptol-like expressions
  * `x # y`
    * --> ```x #`{'n,'m,'a} y```
    * --> `append_seq x y :: ('n + 'm, 'a) seq`
* Type_Args.thy
  * syntax for type signatures
  * `{a,b} (fin a, a > b) => [a] -> [b]`
    * --> `{'a,'b} (fin 'a, 'a > 'b) =?> [a] => [b]`
    * --> `'a tyarg => 'b tyarg => ('a,bool) seq => ('b,bool) seq`
    * constraints like `'a > 'b` are later converted into logical preconditions
  * syntax for type arguments
  * ```f`{a} x``` 
    * --> ```f`{'a} x```
    * --> `f TY('a) x`
* Type_Predicate.thy
  * types and syntax for type constraints
  * `holds :: 'a itself => bool` class field providing the logical interpretation of type `'a`
    * `PRED('a)` --> `holds TYPE('a)`
  * `(a > b, Eq c)`
    * --> `('a > 'b, Eq 'c)`
    * --> `PRED('a > 'b, Eq 'c)` (added as function precondition)
    * --> `PRED(('b,'a) Lt) ∧ PRED('c::coercible_atom) topT)`
    * --> `LENGTH('b) < LENGTH('a)`
* Seq.thy
  * defines `seq` type for representing fixed-length finite Cryptol sequences
  * type syntax for `seq`
  * `[a][b]c`
    * --> `['a]['b]'c`
    * --> `('a, ('b, 'c) seq) seq`
  * defines `seq` operations corresponding to Cryptol primitives
* Seq_Code.thy
  * executable implementation of `seq` type for code extraction
  * implements boolean-valued sequences as `HOL-Library.Word.word` values
  * `quickcheck` instance for `seq`
* ZIntSeq.thy
  * defines the modular arithmetic interpretation of boolean-valued sequences
  * `(x : [n]) + (y : [n])`
    * --> `(x :: ('n,bool) seq) + (y :: ('n,bool) seq)`
    * --> `of_int ((to_int x + to_int y) % (2 ^ LENGTH('n)))`
* WordSeq.thy
  * relates boolean-valued sequences to existing `HOL-Library.Word.word` type
  * lemmas for converting between `seq` and `word` values and operations
  * `(x + y) = word_to_seq (seq_to_word x + seq_to_word y)`
* Cryptol_Definition.thy
  * provides `cryptol_definition` command for additional pre- and post-processing
    of translated Cryptol definitions
    * moves guards from type signatures into definition bodies as preconditions
    * drops redundant coercions after parsing
    * converts type-arguments into function arguments
  * provides `cryptol_termination` command for installing definitions for recursive
    Cryptol functions
      * takes a user-provided proof that the provided Cryptol function terminates
      * internally uses `function` package for defining the underlying constants
* Coercible.thy
  * defines the `coercible` class, for implementing coercions between semantically-equivalent types
  * all `coercible` types must define a projection to and from a universal base type
  * defines `coerce :: 'a => 'b` which projects `'a` values into the universal type, and then 
    projects a `'b` value from the result
  * `coerce` is used to convert from `('n,'a) seq` values to `('m,'a) seq` values, where
    `'n` and `'m` have the same `LENGTH` but are formally distinct.
    * generalizes to nested sequence types
* Coercible_Insts.thy
  * `coercible` instances for all types corresponding to Cryptol primitive types
  * identities for converting `coerce` applications into standard functions
    * `coerce (x :: 'a list) :: 'b list` --> `map (coerce :: 'a => 'b) x`
* Unconstrain.thy
  * tools for manipulating class constraints in theorems and proofs
  * the `constrain` method allows for performing case-split based on a type
    satisfying the constraints of a class

# Word vs. Seq

The `seq` type is a generalization of the existing `HOL-Library.Word.word` type. Specifically, 
a boolean-valued `seq` is isomorphic to a `word` of the same length, with respect to both
arithmetic operations and bit-level functions. The `WordSeq` theory defines the `seq_to_word` and
`word_to_seq` projections, and a corresponding library of lemmas for relating `seq` and `word` operations.
The named theorem `word_seq_convs` contains rewrite rules for converting `seq` proof subgoals into
equivalent `word` subgoals.

## The `len` class constraint

The definition of the `word` type constrains the length parameter to the `len` class, which
requires that the numeric interpretation of the type be non-zero. This effectively constrains
all `word` definitions and lemmas to non-zero length words.

In contrast, zero-length sequences in Cryptol are defined and simply treated as a unit type.
Similarly, the `seq` type is defined for zero-length type parameters. This simplifies the translation
from Cryptol into Isabelle, but introduces some challenges during proofs if we wish to re-use
the existing library of `word` lemmas.

## Constrain and Unconstrain

It is straightforward to perform a case analysis on the length of a `seq` or `word` during a proof.
In the non-zero case we have a logical assumption that `LENGTH('a) > 0`, which is essentially
equivalent to the class constraint `'a::len` but technically distinct. Lemmas with the `len` constraint
will not immediately apply to subgoals with `LENGTH('a) > 0` as an assumption.

The `constrain` method addresses this limitation by creating a copy of the current subgoal, but
replacing the type variables with fresh variables that have additional class constraints. Using
the existing `subgoal` command, we can prove the subgoal with the class constraints in place,
and then lift the result into a local fact. Importantly, this local fact is now generalized over the previously-fixed type parameters.

The `unconstrain_cases` rule attribute can then convert this resulting fact into a form that is directly
applicable to the original subgoal, by converting the class constraint into a logical precondition.

### Example

Given the following Cryptol property:

```
shift_pow : {n} (fin n) => [n] -> Bit
shift_pow x = (x << 1) == (x + x)
```

and corresponding Isabelle definition:

```
cryptol_definition shift_pow :: "{'n} ((fin 'n) =?> ((['n]) ⇒ Bit))" where
"shift_pow x ≡ (x <<`{'n,Integer,Bit} (1 :: Integer)) ==`{['n]} (x +`{['n]} x)"
```

We easily can prove `shift_pow` for any length:

```
lemma "shift_pow`{'n} x"
  unfolding shift_pow_def
  apply (constrain 'n="'nn::len")
   subgoal H 
   (* non-zero length case *)
   by (simp add: word_seq_convs shift_rotate_word_defs)
  apply (rule H[unconstrain_cases])
  by simp (* zero-length case *)
```
# Coercions

In contrast to Cryptol, Isabelle's type system does not consider types to be identical
when they have the same numeric interpretation. Cryptol's implicit type coercions
between equivalent types must be made explicit in the Isabelle representation.

# Example

The following property can be proven by Cryptol for small bitvector lengths:

```
add_int : {n,m} (fin n, n == m) => [n] -> [m] -> Bit
add_int x y = fromInteger (toInteger x + toInteger y) == x + y
```

The constraint `n == m` allows the expression `x + y` to be type-correct in Cryptol, despite
`x` and `y` having syntactically distinct types. The translation into Isabelle is straightforward,
and includes the types inferred by Cryptol when during typechecking.

```
cryptol_definition add_int :: "{'n,'m} ((fin 'n,'n = 'm) =?> ((['n]) ⇒ ((['m]) ⇒ Bit)))" where
"add_int x y ≡ (fromInteger`{['n]} ((toInteger`{['n]} x) +`{Integer} (toInteger`{['m]} y))) ==`{['n]} (x +`{['n]} y)"
```

In contrast to Cryptol, the constraint guard `'n = 'm` does not allow Isabelle to treat the types
`'n` and `'m` as identical. This is a logical precondition to the function, only requiring that
`LENGTH('n)` and `LENGTH('m)` yield the same `nat` value. Consequently, the
expression `(x :: ['n]) + (y :: ['m])` is not type-correct in Isabelle, regardless of any logical
preconditions.

To address this limitation, the Cryptol syntax in Isabelle implicitly wraps most function
arguments with `coerce :: 'a => 'b`, provided by the `Coercible` theory. The
`coercible` instances for `'a` and `'b` together define how to `coerce` between the two types.
For incompatible types, the result is the undefined expression: `invalid_coercion TYPE('a) TYPE('b)`.

Coercions effectively allow most expressions to be trivially type-correct by instead deferring
type-checking to the logic. In our example, translation-specific syntax ```x +`{['n]} y``` is parsed 
as `(x : ['n]) + (y : ['n])`, which desugars into `(coerce x :: ['n]) + (coerce y :: ['n])`.

After parsing, the full definition of `add_comm` expands into:

```
('n topT,'n = 'm) ⇒ from_int (to_int x + to_int y) = x + (y : ['n])
```

The `cryptol_definition` command has performed two post-processing steps here: the guard
has been moved from the signature into the definition body, and the redundant coercion
`x : ['n]` has been dropped. The Cryptol library provides lemmas for reasoning about
coercions, usually by rewriting the general `coerce` function into a more specific
form based on the types involved. In this case, we can rewrite `y : ['n]` into
`word_to_seq (UCAST('m → 'n) (seq_to_word y))` using the lemma `WordSeq.coerce_seq_len_ucast`.





