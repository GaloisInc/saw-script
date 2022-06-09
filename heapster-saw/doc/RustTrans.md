
# Rust-to-Heapster Translation

FIXME: Rust translates to a subset of Heapster, as described in this document

## Translating Expression Types

Unlike in many languages where types describe program values, Rust types in fact
describe the shape and structure of blocks of memory. Each Rust variable
designates a block of memory where the value of the variable is stored. The type
of the variable then describes the shape of that memory. Thus, Rust types are
translated to Heapster shape expressions, which Heapster uses to describe
memory. Heapster shapes are documented [here](Permissions.md).

The basic conversion from Rust is described in the following table, though Rust
implements a number of layout optimizations, described below, that alter this
translation. In this table, we write `[| T |]` for the translation of Rust type
`T` to a Heapster shape, and we write `len(sh)` for the Heapster expression
giving the length of Heapster shape `sh`, when this is defined. The notation
`[\| Name \|]` denotes the translation of the type definition associated with
type name `Name`, as defined in the next section.


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

Rust function definitions are written like this:

```
fn foo <'a1,...,'am> (x1 : T1, ..., xn : Tn) -> T { ... }
```

This defines `foo` as a function that is polymorphic over `m` lifetimes that
takes `n` input arguments of types `T1` through `Tn` to an output value of type
`T`. Note that Rust function types can in general be polymorphic over type
variables as well, but Rust compilation to LLVM always monomorphizes these
polymorphic function types, so Heapster, which runs on LLVM code, never sees
these polymorphic types. In Heapster, we write the type of this function as:

```
<'a1,...,'am> fn (x1 : T1, ..., xk : Tk) -> T
```

where the variable names are optional. For technical reasons, Rust does not
actually allow polymorphic function types, but only supports non-polymorphic
functions types, starting with the `fn` keyword, so this is a syntactic
extension supported by Heapster.

Rust function types are translated to Heapster function types in two steps. The
first step is argument layout. Argument layout takes the translations of the
Rust argument types to Heapster shapes, which describe the shape of memory
blocks, and lays out those memory block shapes onto register values. At a high
level, this step can be seen as bridging the gap between Rust types, which
describe blocks of memory, and LLVM types, which describe values. The second
step is to add lifetime permissions. This step generates lifetime ownership
permissions for each of the lifetime variables `'ai` in the Rust function type.


FIXME: give some examples of how some simple Rust function types are translated
to Heapster


### Argument Layout

Argument layout converts a shape, which describes the layout and associated
permissions of a memory block, to a permission on a sequence of register values,
if this is possible. Note that this concept is different from the Rust concept
of "type layout", though the two are related. In fact, the notion of argument
layout described here is very undocumented in Rust, and has in fact been
determined by consulting a number of blog posts and by much experimentation.

In Heapster (as in the underlying Crucible type system), sequences of values are
called structs and a permission on a sequence of values is called a struct
permission. Argument layout is thus defined as a partial function `Lyt(sh)` that
maps a Heapster shape `sh` for a particular function argument to a permission of
type `perm(struct(tp1,...,tpn))` for some value types (i.e., Crucible types)
`tp1` through `tpn`. When the layout of the type `T` of an argument is not
defined --- e.g., if `T` is too big to fit in registers or it is a slice or
other dynamically-sized type that has no well-defined size --- then the
corresponding argument is represented as a pointer to a block of memory with the
shape defined by `T`.

In order to define `Lyt(sh)`, we first define two helper operations on structure
permissions. Both of these are partial functions that take in two structure
permissions, possibly of different types, and return a structure permission with
some potentially different type. The first of these is the struct permission
append operator `p1 ++ p2`, which combines a struct permission `p1` of type
`perm(struct(tp1,...,tpm))` and `p2` of type `perm(struct(tp1',...,tpn'))` into
a permission of type `perm(struct(tp1,...,tpm,tp1',...,tpn'))` on the append of
structs with permissions `p1` and `p2`. This operation is defined as follows:

| Permissions `p1` and `p2` to Append | Resulting Permission `p1++p2` |
| ------------------------ | --------------------- |
| `struct(p1,...,pn) ++ struct(q1,...,qm)` = | `struct(p1,...,pn,q1,...,qm)` |
| `(p1 or p2) ++ q` = | `(p1 ++ q) or (p2 ++ q)` |
| `p ++ (q1 or q2)` = | `(p ++ q1) or (p ++ q2)` |
| `(exists z. p) ++ q` = | `exists z. (p ++ q)` |
| `_ ++ _` = | Undefined otherwise |

The second operation on structure permissions needed here is the disjucntion
operation `p1 \/ p2`. Intuitively, this operation takes the disjunction of the
two struct permissions `p1` and `p2` after first equalizing the number of
registers they refer to. More formally, this `p1 \/ p2` is defined as follows:

* If `p1=struct(p1')` and `p2=struct(p2')` where `p1'` and `p2'` have the same
  type, then `p1 \/ p2=struct(p1' or p2')`;

* If there is a permission `p1' = p1 ++ struct(true,true,...,true)` of the same
 type as `p2`, then `p1 \/ p2` is defined as the disjunction `p1' or p2`;

* If there is a permission `p2' = p2 ++ struct(true,true,...,true)` of the same
 type as `p1`, then `p1 \/ p2` is defined as the disjunction `p1 or p2'`;

* Otherwise, `p1 \/ p2` is undefined.

Using these operations, the layout function `Lyt(sh)` is defined as follows:

| Heapster shape | Its layout as a struct permission |
|--------------|--------------------------|
| `Lyt(emptysh)` =           | `struct()` |
| `Lyt(Name<args>)`  = |  `Lyt(unfold(Name,args))` |
| `Lyt(fieldsh(p))`       = |  `struct(p)` |
| `Lyt(arraysh(k,stride,sh))` = | `Lyt(sh;...;sh)` for `k` copies of `sh`, if `8*len(sh)=stride` |
| `Lyt(arraysh(_,_,_))` = | undefined otherwise |
| `Lyt(sh1 ; sh2)`      = | `Lyt(sh1) ++ Lyt(sh2)` |
| `Lyt(sh1 orsh sh2)`  = | `Lyt(sh1) \/ Lyt(sh2)` |
| `Lyt(exsh z. sh)` = | `exists z. Lyt(sh)` |
| `Lyt(falsesh)` =  | `false` |

The empty shape is laid out as a struct permission on an empty list of fields.
Named shapes are laid out by laying out their unfolding. Field shapes are laid
out as a struct permission with a single field whose permission is given by the
permission in the field shape. Array shapes with a known, fixed size `k` are
laid out as `k` copies of their shape. Otherwise, array shapes with a
dynamically-determined length are not laid out as arguments. Sequence and
disjunctive shapes are laid out using the `++` and `\/` operations defined
above, respectively, while existential shapes are laid out as existential
permissions and the false shape is laid out as the false permission.

Using the `Lyt(sh)` function, we define the argument layout function `Arg(sh)`
that maps `sh` to a sequence of arguments and their corresponding permissions.
The Rust compiler uses the convention that any type that fits in no more than
two argument values is laid out into argument values, and otherwise is passed by
pointer. To handle this convention, `Arg(sh)` returns permissions for up to two
argument values if `Lyt(sh)` returns a struct permission with at most two
fields, and otherwise returns a `memblock` permission describing a pointer to a
memory block of shape `sh`. More formally, `Arg(sh)` is a function from shape
`sh` to a sequence of normal and ghost arguments with permissions, defined as
follows:

* If `Lyt(sh)=struct(p1,...,pn)` for a sequence `p1,...,pn` of 0, 1, or 2
  permissions, then `Arg(sh)=arg1:p1,...,argn:pn`;

* If `Lyt(sh)=p` for `p` of type `perm(struct(tp1,...,tpn))` for a sequence
  `tp1,...,tpn` of 0, 1, or 2 types, then
  `Arg(sh)=ghost:p,arg1:eq_proj(ghost,1),...,argn:eq_proj(ghost,n)`;

* If `Lyt(sh)` is undefined but `len(sh)=ln`, then `Arg(sh)=arg:memblock(W,0,ln,sh)`;

* Otherwise, `Arg(sh)` is undefined.

The complexity of the second case comes from the case where `Lyt(sh)` returns a
struct permission where the permissions on the individual fields are cannot be
separated from each other. In this case, `Arg(sh)` returns a ghost variable
`ghost` to specify the tuple of the arguments, each of which are required to
equal their corresponding projection of `ghost` using `eq_proj` permissions.

The argument layout function `Arg(sh)` is extended to multiple arguments with
the argument sequence layout function `Args(sh1,...,shn)`. For any sequence
`sh1,...,shn` of shapes for `n` input arguments, we define the
`Args(sh1,...,shn)` as the sequence of permissions on regular and ghost
arguments given by `Arg(sh1),...,Arg(shn)`, if all of these are defined.

We define the return value layout function `Ret(sh)` as a partial function from
a shape `sh` to a permission on the return value `ret` of a funciton as follows:

* If `Lyt(sh)=struct(p)` for a single permission `p`, then `Ret(sh)=ret:p`;

* If `Lyt(sh)=p` for `p` of type `perm(struct(tp1,...,tpn))` for a sequence
  `tp1,...,tpn` of 0, 1, or 2 types, then `Ret(sh)=ret:p`;

* Otherwise, `Ret(sh)` is undefined.

We can then define the function type layout `FnLyt(sh1,...,shn,sh)` of a
sequence of `n` shapes for input arguments and a shape `sh` for the return value
as follows:

* If `Ret(sh)=ret:p` and `Args(sh1,...,shn)` is defined, then
  `FnLyt(sh1,...,shn,sh)` is defined as the Heapster function permission
  `Args(sh1,...,shn) -o ret:p` that takes in the regular and ghost arguments
  specificed by `Args(sh1,...,shn)` and returns a value `ret` with permission
  `p`;

* If `Ret(sh)` is undefined but `Args(sh1,...,shn)` is defined and `len(sh)=ln`, then
  `FnLyt(sh1,...,shn,sh)` is defined as the Heapster function permission
  ```
  arg0:memblock(W,0,ln,emptysh),Args(sh1,...,shn) -o  arg0:memblock(W,0,ln,emptysh)
  ```

* Otherwise, `FnLyt(sh1,...,shn,sh)` is undefined.


### Adding Lifetime Permissions

FIXME: explain the two steps, lifetime lifting and building the lifetime
ownership permissions

The lifetime lifting function `LtLift(p)` maps a permission `p` to a lifted
permission along with 0 or more fresh ghost variables with permissions on them.
Intuitively, this operation finds permissions contained inside `p` that use any
of the lifetime variables of a function type, and lift those permissions to
permissions on fresh ghost variables. This allows the permission type for a
function to refer to just those values inside a more complicated type that
depend on a particular lifetime.

FIXME: example

To define the lifetime lifting function, we first define the lifetime lifting
contexts as follows:

```
L ::= _ | [l]ptr((rw,off) |-> L) * p1 * ... * pn | [l]memblock(rw,off,len,Lsh) * p1 * ... * pn
Lsh ::= _ | sh1;Lsh | Lsh;sh2 | fieldsh(L) | ptrsh(rw,l,Lsh)
```

FIXME: describe the process of lifting

FIXME: explain the operation `LtPerms(a)(x:p)`, defined as follows:

* For conjunctions, the operation returns only those conjuncts that contain
  lifetime `a`, meaning that `LtPerms(a)(x:p1*...*pn)=x:p(i1)*...*p(ik)` where
  `i1,...,ik` is the sequence of indices `i` such that `pi` contains lifetime
  variable `a` free;

* If `p` is not a conjunction but contains `a` free, then `LtPerms(a)(x:p)=x:p`;

* Othersise, `LtPerms(a)(x:p)` is the empty sequence `()`.

To add a lifetime permission to a function type `ps_in -o ps_out`, we define the
function

```
AddLt(a)(ps_in -o ps_out) =
  let a_ps_in = absMods(a)(LtPerms(a)(ps_in)) in
  a:lowned(a_ps_in), ps_in -o a:lowned(LtPerms(a)(ps_out) -o a_ps_in)
```

FIXME: explain the above; also define `absMods(a)(ps)` as the funciton that
abstracts all the read/write and lifetime modalities in `ps`

To add multiple lifetime permissions to a function type, we define

```
AddLts(a1,...,an)(ps_in -o ps_out) =
  AddLt(a1)(AddLt(a2)(... AddLt(an)(ps_in -o ps_out)))
```

Putting all the pieces together, we define the translation of a Rust function
type as follows:

```
[| <'a1,...,'am> fn (x1 : T1, ..., xk : Tk) -> T |] =
  AddLts(a1,...,an)(LtLift(FnLyt([| T1 |], ..., [| Tn |], [| T |])))
```
