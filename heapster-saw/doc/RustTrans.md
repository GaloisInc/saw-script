
# Rust-to-Heapster Translation

In this document, we describe the automated translation from Rust types to
Heapster permissions. Because some of the details of how Rust types are laid out
in memory are not explicitly defined by the Rust specification, some of this
translation has been informed by experimentation with how Rust compiles various
functions and types, so may not be entirely complete or accurate, but it so far
seems to work in most cases.


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
| `&mut 'a [T]` | see below |
| `&mut 'a T` | `[a]ptrsh(W,[\| T \|])` if `T` is not a DST |
| `&'a [T]` | see below |
| `&'a T` | `[a]ptrsh(R,[\| T \|])` if `T` is not a DST |
| `[T;N]` | `arraysh(N, [\| T \|])` |
| `(T1,...,Tn)` | `[\| T1 \|] ; ... ; [\| Tn \|]` |
| `Name<'a1,...,'am,T1,...,Tn>` | `[\| Name \|] (a1, ..., am, [\| T1 \|], ..., [\| Tn \|])` |
| `!` | `falsesh` |


Types of the form `&mut 'a [T]` and `&'a [T]` are treated specially in Rust,
because these are references to a slice type `[T]` of unknown size. In Rust,
types with unknown size are called _dynamically sized types_ or DSTs. These
require special treatment in order to ensure that dereferences are always
bounds-checked to be in the bounds of the slice. To make this possible,
references to DSTs are always "fat pointers" that are a pointer value along with
an integer value that says how many elements are in the slice pointed to by the
pointer. Thus, the type `&mut 'a [T]` is translated as follows:

```
exsh n:bv 64.[a]ptrsh(W,arraysh(n,[| T |]));eq(llvmword(n))
```

This shape says there exists an `n` such that the first field in a memory block
of this shape points to an array of `n` elements, each of which have shape
`[| T |]`, while the second field is an LLVM word value equal to `n`. Read
references `&'a [T]` to slices are translated similarly, but with read instead
of write pointer shapes.



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
  (fieldsh(eq(llvmword(0))) ; [| T1_1 |] ; ... ; [| T1_k1 |]) orsh
  (fieldsh(eq(llvmword(1))) ; [| T2_1 |] ; ... ; [| T2_k2 |]) orsh
  ...
  (fieldsh(eq(llvmword(l-1))) ; [| Tl_1 |] ; ... ; [| Tl_kl |])
```

(NOTE: Technically speaking, this translation assumes the enum has been
flagged with the `#[repr(C,u64)]` pragma to indicate that the discriminant is a
64-bit integer and that the type is laid out in a C-compatible manner.)


## Niche Optimization

As an optimization, Rust has one exception to the rules given above for enums
that is called _niche optimization_. To define niche optimization, we first
define the notion of an _option-like_ enum, which is an enum type that has one
constructor with a field of some type `T` and one constructor with no fields.
The type `T` is called the _payload_ of the option-like enum type. The primary
example is the type `Option<T>`, defined (in the Rust standard library) as
follows:

```
enum Option<X> { None, Some (X) }
```

A _niche_ in a type `T` is any bit pattern with the same size as `T` but that is
disallowed by the shape requirements of `T`. For instance, the `Box` and
reference pointer types in Rust are required to be non-null, so the null value
is a niche for these types. Similarly, an enum type with `N` fields, numbered
`0` through `N-1`, has a niche where the discriminant is set to the value `N`.

The high-level idea of niche optimization is that the fieldless constructor of
an option-like type can be represented by a niche value in its payload type.
This reduces the size of the elements of this type by eliminating the need for
its discriminant. Thus, for example, the `Option` Rust type is translated to the
following cases:

```
Option<[a]ptr((rw,off) |-> p)> = eq(llvmword(0)) or [a]ptr((rw,off) |-> p)
Option<(fieldsh(eq(llvmword(0)));sh0) orsh ... orsh (fieldsh(eq(llvmword(n)));shn)> =
  (fieldsh(eq(llvmword(0)));sh0) orsh ... orsh (fieldsh(eq(llvmword(n)));shn)
  orsh fieldsh(eq(llvmword(n+1)))
Option<X> =
  fieldsh(eq(llvmword(0))) orsh (fieldsh(eq(llvmword(1)));X)
```


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
The remainder of this section illustrates this translation process through some
examples, and then defines each of the two function type translation steps in
detail.


### How Function Types are Translated

For function types with no lifetimes whose arguments and return values all fit
into a single register (which we assume is 64-bits), the translation is
straightforward. For example, consider the following `box_read` function, that
reads a 64-bit unsigned value from a `Box` pointer:

```
fn box_read (p:Box<u64>) -> u64 { *p }
```

The type of `box_read` is `(Box<u64>) -> u64`, which translates to the Heapster
function type

```
arg0:ptr((W,0) |-> exists z. eq(llvmword(z))) -o arg0:true, ret:exists z. eq(llvmword(z))
```

This type says that the first and only argument, `arg0`, is a pointer to an LLVM
word value when the function is called. More specifically, the permission
`exists z.eq(llvmword(z))` describes an LLVM value that is a word, or numeric,
value, as opposed to a pointer value. Because it is so common, Heapster scripts
often define the abbreviation `int64<>` for this permission, and we shall use
this abbreviation in the remaining examples here. The return value `ret` for our
example is also an LLVM word value. On return, no permissions are held on the
`arg0` value, reflecting the fact that the `Box` pointer passed into `box_read`
is deallocated by that function.

If an argument type does not fit into a single register but does fit into two
registers, Rust will lay it out across two argument values at the LLVM level.
For example, let us define a struct type `Pair64` of pairs of 64-bit integers
and a function `pair_proj1` to project out the first element of such a struct as
follows:

```
struct Pair64 { proj1 : u64, proj2 : u64 }

fn pair_proj1 (p:Pair64) -> u64 { p.1 }
```

The `Pair64` structure fits into two 64-bit registers, so the type of
`pair_proj1` is translated to the Heapster type

```
arg0:int64<>, arg1:int64<> -o ret:int64<>
```

Note that, if the input or output permission on an argument is the vacuous
permission `true`, it can be omitted, so the above permission states that no
permissions are returned with the argument values `arg0` and `arg1`.

If the return value fits into two registers, Rust returns it as a two-element
structure, so, for instance, the Rust function type `fn (Pair64) -> Pair64`
translates to the Heapster type

```
arg0:int64<>, arg1:int64<> -o struct(int64<>,int64<>)
```

Fieldless enums, which is the Rust name for enum types where none of the
constructors has any fields, can be laid out in a single register for the
discriminant. For enum types with fields, if all the fields of each constructor
of an enum fit into a single register, then the entire enum is laid out as two
registers, one for the discriminant and one for the field(s) of the
corresponding constructor. This type is a little more complicated to represent
in Heapster, because the disjunction for the enum must apply to multiple values
at the same time. This is accomplished using a ghost variable of struct type,
and stating the the individual arguments equal its projections. For example, if
we define the enum

```
#[repr(C,u64)] pub enum Sum<X,Y> { Left (X), Right (Y) }
```

then the type `fn (Sum<(),u64>) -> u64` is translated as follows:

```
ghost:(struct(eq(llvmword(0)),true) or struct(eq(llvmword(1)),int64<>)),
arg0:eq_proj(ghost,0), arg1:eq_proj(ghost,1)
-o
ret:int64<>
```

This type says that, on input, the first and second arguments are the first and
second projections, respectively, of some struct given by a ghost variable
`ghost`. The permissions on `ghost` say that either its first field equals `0`
and its second field is unconstrained, corresponding to the `Left` constructor
of the `Sum` type, or its first field equals `1` and its second field is a
64-bit integer, corresponding to the `Right` constructor. As before, the output
permissions are `int64<>` for the return value and no permissions for the input
arguments.

If the type of an argument does not fit into two registers, Rust passes it by
pointer. That is, if an argument has a type `T` that does not fit into two
registers, then it is treated as if it had type `Box<T>`. For example, if we
define the struct type

```
struct Triple64 { triple1:u64, triple2:u64, triple3:u64 }
```

then the type `fn (Triple64) -> u64` is translated to

```
arg0:memblock(W,0,24,Triple64<>) -o ret:int64<>
```

where the named shape `Triple64<>` is defined as the sequence

```
fieldsh(int64<>);fieldsh(int64<>);fieldsh(int64<>)
```

of three field shapes containing 64-bit integers. The `memblock` input
permission has size `24` because `Triple64<>` has three 8-byte fields, for a
total size of 24 bytes.

If the return value does not fit into two registers, its value is written to a
pointer that is passed as the first argument. So, for instance, the function
type `fn (Triple64) -> Triple64` is translated to

```
arg0:memblock(W,0,24,true), arg1:(W,0,24,Triple64<>) -o arg0:(W,0,24,Triple64<>)
```

This indicates that, on input, `arg0` points to a 24-byte memory block. The
`true` shape indicates that this block can be uninitialized, i.e., that no
constraints are made on its shape. The actual input argument of type `Triple64`
is passed as `arg1`. On output, permissions to `arg1` are dropped, but
permissions to `arg0` are changed to have the shape `Triple64<>` of the return
type.

The remaining complexity in translating function types to Heapster is in
handling lifetimes. This works by adding lifetime ownership permissions to both
the input and output permissions for each lifetime `'a` in the Rust function
type, indicating that lifetime `'a` is active at the start of the function and
when it returns. The input lifetime ownership permission for `'a` says that each
of the permissions mentioning lifetime `'a` has been borrowed from some other,
larger lifetime that is outside of `'a`. The output lifetime ownership
permission for `'a` says that these same permissions are still borrowed by `'a`
from the same outer lifetimes, but that all of those permissions have been
"given back" to `'a` except for those permissions in the output permissions that
still mention `'a`.

In more detail, recall that a lifetime ownership permission has the form
`a:lowned (ps_in -o ps_out)`. This permission indicates that lifetime `a`
"holds" or "contains" permissions `ps_out`, and is current "leasing out" or
"lending" permissions `ps_in`. Once all of the lent permissions `ps_in` are
returned to lifetime `a`, that lifetime can be ended, and the permissions
`ps_out` that it holds can be recovered. The input lifetime ownership permission
used for `a` has the form `a:lowned (ps_a_in -o ps_a_abs)`, where `ps_a_in` is
the list of all permissions containing `a` in the input of the translated Rust
function type, and `ps_a_abs` is the result of replacing each occurrence of `a`
and its accompanying read/write modality with fresh variables. (NOTE: the actual
input lifetime ownership permission computed by Heapster is the simplified
lifetime ownership permission `a:lowned(ps_a_abs)`, which is logically
equivalent to the above but has a simpler translation.) The output
lifetime ownership permission is `a:lowned (ps_a_out -o ps_a_abs)`, where
`ps_a_out` is the list of all permissions containing `a` in the output of the
translated Rust function type.

For example, consider the accessor function

```
fn <'a> pair_proj1_ref (p:&mut 'a Pair64) -> &mut 'a u64 { &mut p.1 }
```

that takes a mutable reference to a `Pair64` and returns a mutable reference to
its first element. The translation of the type of `pair_proj1_ref`, which is the
function type `<'a> fn (&mut 'a Pair64) -> &mut 'a u64`, is the Heapster type

```
a:lowned(arg0:[a]ptr((W,0) |-> Pair64<>) -o arg0:[l]ptr((rw,0) |-> Pair64<>)),
arg0:[a]ptr((W,0) |-> Pair64<>)
-o
a:lowned(ret:[a]ptr((W,0) |-> int64<>) -o arg0:[l]ptr((rw,0) |-> Pair64<>)),
ret:[a]ptr((W,0) |-> int64<>)
```

The input permissions say that `arg0` is a writeable pointer to a `Pair64`
structure, that is only valid while lifetime `a` is active. Further, the input
lifetime ownership permission for `a` says that, when the function is called,
`a` holds pointer permissions to `arg0` relative to some other lifetime `l`, and
is currently lending pointer permissions to `arg0` relative to `a`. The output
permissions say that the return value `ret` is a writeable pointer to a 64-bit
integer that is relative to lifetime `a`. The output lifetime permission for `a`
says that `a` holds the same pointer permission relative to lifetime `l` as on
input, but is only lending out the pointer held by `ret`.

If a permission containing lifetime `a` is inside another permission, it is
lifted to the top level by creating a ghost variable that holds that permission.
For instance, the type `<'a> fn (Box<&'a u64>) -> u64` is translated to the
Heapster type

```
a:lowned(z:[a]ptr((R,0) |-> int64<>) -o z:[l]ptr((rw,0) |-> int64<>)),
arg0:ptr((W,0) |-> eq(z)), z:[a]ptr((R,0) |-> int64<>)
-o
a:lowned(empty -o z:[l]ptr((rw,0) |-> int64<>)),
ret:int64<>
```

In this case, `z` is a ghost variable used to represent the pointer value
pointed to by `arg0` for which a pointer permission in lifetime `a` is held. As
before, the input lifetime ownership permission for `a` specifies that pointer
permissions for `z` relative to some outer lifetime `l` are held by lifetime
`a`, which is currently lending out a copy of those permissions relative to
lifetime `a`. Since there are no occurrences of `a` in the output Rust type, the
output lifetime ownership permission for `a` indicates that `a` is not lending
any permissions on return from the function, indicated with the `empty`
permissions list.


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

Adding lifetime permissions to the translation of a Rust function type is done
in two steps. The first step, lifetime lifting, lifts permissions containing a
lifetime to the top level. The second step constructs the required lifetime
ownership permissions.

For the first step, the lifetime lifting function `LtLift(p)` maps a permission
`p` to a lifted permission along with 0 or more fresh ghost variables with
permissions on them. Intuitively, this operation finds permissions contained
inside `p` that use any of the lifetime variables of a function type, and lift
those permissions to permissions on fresh ghost variables. This allows the
permission type for a function to refer to just those values inside a more
complicated type that depend on a particular lifetime.

To define the lifetime lifting function, we first define the lifetime lifting
contexts as follows:

```
L ::= _ | [l]ptr((rw,off) |-> L) * p1 * ... * pn | [l]memblock(rw,off,len,Lsh) * p1 * ... * pn
Lsh ::= sh1;Lsh | Lsh;sh2 | fieldsh(L) | ptrsh(rw,l,Lsh)
```

Each lifetime lifting context `L` is a permission with a single occurrence of a
"hole" of the form `_`. Similarly, a lifetime lifting shape context `Lsh` is a
shape containing a single occurrence of a hole inside one of its field
permissions. We write `L[p]` and `Lsh[p]` for the result of replacing the hole
`_` with `p` in `L` or `Lsh`, respectively. Intuitively, a hole describes an
occurrence of a permission inside a larger permission or shape that can be
lifted to a top-level ghost variable. Holes are only allowed inside a pointer
permission or the shape of a block permission; specifically, they are not
allowed inside disjunctive or array permissions, because there could be zero or
multiple values corresponding to that permission, and lifetime lifting is only
supposed to lift a single value.

If any permission `p` can be written as `L[p']` for some `L` that is not the
trivial context `_` and some `p'` containing a free lifetime variable, then we
say that the permission `L[eq(z)]` along with the permission assignment `z:p'`
for fresh ghost variable `z` is a _lifetime lifting_ of `p`. We then define the
lifetime lifting function `LtLift(p)` from permission `p` to a permission plus
a sequence of zero or more ghost variables with permissions as follows:

* If `p` has a lifetime lifting `L[eq(z)]` and `z:p'` such that `p'` itself has
  no lifetime lifting, then `LtLift(p)` returns `LtLift(L[eq(z)])` along with
  `z:p'`;

* Otherwise, `LtLift(p)` just returns `p` itself.

The `LtLift()` function is then extended to lists of permissions
`x1:p1,...,xn:pn` by applying it pointwise to the individual permissions `p1`
through `pn`.


For the second step of adding lifetime permissions to the translation of a Rust
function type, we first define the operation `LtPerms(a)(x:p)` that finds all
permissions containing lifetime `a` in the permission assignment `x:p`. This is
defined as follows:

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
  let ps_a_in = LtPerms(a)(ps_in) in
  let ps_a_abs = absMods(a)(ps_a_in) in
  a:lowned(ps_a_in -o ps_a_abs), ps_in -o a:lowned(LtPerms(a)(ps_out) -o a_ps_in)
```

The function `absMods(a)(ps)` abstracts each occurrence of lifetime `a` and its
associated read/write modality by instantiating them with fresh ghost variables.
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
