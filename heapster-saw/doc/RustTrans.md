
# Rust-to-Heapster Translation

FIXME: Rust translates to a subset of Heapster, as described in this document

## Translating Expression Types

Unlike in many languages where types describe program values, Rust types in fact
describe the shape and structure of blocks of memory. Each Rust variable
designates a block of memory where the value of the variable is stored. The type
of the variable then describes the shape of that memory. Thus, Rust types are
translated to Heapster shape expressions, which Heapster uses to describe
memory. Heapster shapes are documented [here](Permissions.md). The basic
conversion from Rust is described in the following table, though Rust implements
a number of layout optimizations, described below, that alter this translation.
In this table, we write `[| T |]` for the translation of Rust type `T` to a
Heapster shape, and we write `len(sh)` for the Heapster expression giving the
length of Heapster shape `sh`, when this is defined. The notation `[\| Name \|]`
denotes the translation of the type definition associated with type name `Name`,
as defined in the next section.


| Rust Type | Translation to a Heapster Shape |
|--------|--------------------|
| `Box<T>` | `ptr((W,0) \|-> [\| T \|])` |
| `&mut 'a T` | `[a]ptr((W,0) \|-> [\| T \|])` |
| `&'a T` | `[a]ptr((R,0) \|-> [\| T \|])` |
| `[T]` | `exists n:bv 64. arraysh(n, len([\| T \|]), [\| T \|])` |
| `(T1,...,Tn)` | `[\| T1 \|] ; ... ; [\| Tn \|]` |
| `Name<'a1,...,'am,T1,...,Tn>` | `[\| Name \|] (a1, ..., am, [\| T1 \|], ..., [\| Tn \|])` |
| `!` | `falsesh` |

FIXME: describe the above


## Translating Type Definitions

Rust includes type definitions for structure and enumeration types, which allow
the user to define a type name `Name` as either a sequence of Rust types or a
tagged disjunction of sequences of Rust types, respectively. These type
definitions can be polymorphic, meaning that the can quantify over Rust
lifetimes and types. They can also be recursive, meaning the definition of
`Name` can include `Name` itself.

Both structure and enumeration types are translated to Heapster by using the SAW
command

```
heapster_define_rust_type env "...Rust type definition..."
```

This command adds a Heapster named shape to the current Heapster environment
`env` with the same name as the Rust type definition.


Rust structure types are written

```
pub struct Name<'a1,...,'am,X1,...,Xn> { fld1 : T1, ..., fldn : Tn }
```

This type is essentially a sequence type, and is translated to a Heapster named
shape defined as follows:
```
Name<a1,...,am,X1,...,Xn> = [\| T1 \|] ; ... ; [\| Tn \|]
```
As with the translation of Rust tuple types, this translates a Rust structure
type to the sequence shape built from sequencing the translations of the
structure fields. Note that Heapster named shapes can be recursive, which is the
case is the original definition of `Name` is recursive.


Rust enumeration types are written

```
enum Name<'a1,...,'am,X1,...,Xn> {
  Ctor1 (T1_1,...,T1_k1),
  Ctor2 (T2_1,...,T2_k2),
  ...
  Ctorl (Tl_1,...,Tl_kl)
}
```

This defines `Name` as a disjunctive type, whose elements are sequences of one
of the lists `Ti_1, ..., Ti_ki` of types. To identify which of these disjunctive
cases holds for a particular block of memory, the block always starts with a
tag, also called a _discriminant_, that is an integer in the range `0,...,l-1`.
An enumeration type like the above is translated to Heapster as follows:

```
Name<a1,...,am,X1,...,Xn> =
  (fieldsh(eq(0)) ; [| T1_1 |] ; ... ; [| T1_k1 |]) orsh
  (fieldsh(eq(1)) ; [| T2_1 |] ; ... ; [| T2_k2 |]) orsh
  ...
  (fieldsh(eq(l-1)) ; [| Tl_1 |] ; ... ; [| Tl_kl |])
```

(NOTE: Technically speaking, this translation assumes the enum has been
flagged with the `#[repr(C,u64)]` pragma to indicate that the discriminant is a
64-bit integer and that the type is laid out in a C-compatible manner.)


## Layout Optimizations

FIXME: Option-like types

## Translating Function Types

FIXME:
- explain layout (types that take more than two fields become pointers)
- explain lifetimes
