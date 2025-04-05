Summary of Metavariables
========================

In this document, we use the following metavariables to refer to different sorts of data.

  **Metavariable**   | **Description**
  ------------------ | --------------------------------
  `a`                | Permission type
  `e`                | Permission expression
  `b`, `w`           | Bitvector expression
  `x`                | Permission expression variable
  `rw`               | ReadWrite modality expression
  `sh`               | Shape expression
  `l`                | Lifetime expression
  `p`                | Value permission



Value Types
================

The Heapster value types include the regular crucible types as well as heapster-specific types:

| **Permission Types `a`** | **Description** |
| :---: | :--- |
| `unit`                | Crucible unit type |
| `bool`                | Crucible boolean type |
| `nat`                 | Crucible type of natural numbers  |
| `bv w`                | Crucible bitvector type of width `w` |
| `struct(a1,..,an)`    | Crucible struct type \[equivalent to a tuple, not to be used for C structs\] |
| `llvmptr w`           | llvm-specific crucible type of pointers of width `w` |
| `rwmodality`          | type of modality for read or write permissions |
| `permlist`            | type of a list of permissions - outdated |
| `llvmframe w`         | type of ghost objects that represent the current stack frame with respect to bitvectors of width `w` |
| `perm(a)`             | type of permissions describing how to use an object of type `a`. That is, the proposition `x:p` for a permission `p` of type `perm(a)` means "`a` value `x` of type `a` has permission `p`". |
| `llvmshape w`         | type of shapes with respect to bitvectors of width `w` |
| `llvmblock w`         | type of blocks of memory with respect to bitvectors of width `w` |

Permission expressions
======================

Expressions that are considered \"pure\" for use in permissions.

A llvm-pointer (aka an llvm value) is either an llvmword or a variable+an offset

Any crucible type can have a variable of that type, and that thing is an expression

| Permission Expressions `e` | Type | Description |
| :---: | :---: | :--- |
| `x`                          | any                | Any expression variable |
| `unit`                       | `unit`             | A unit literal |
| `b`                          | `bool`             | A literal boolean value |
| `n`                          | `nat`              | A literal natural number |
| `n`                          | `bv w`             | A literal bitvector |
| `b1 + b2`                    | `bv w`             | Sum of two bitvectors |
| `-b`                         | `bv w`             | 2's complement negation of a bitvector |
| `b1 * b2`                    | `bv w`             | Linear multiplication of two bitvectors, meaning that one of the operands must be a constant |
| `struct(e1,..,en)`           | `struct(a1,..,an)` | A (crucible) struct is a tuple of expressions for each argument of the struct type. Crucible structs are different from C structs, and we only use crucible structs when we need to, otherwise C structs are described manually as pointers into chunks of memory |
| `llvmword(e)`                | `llvmptr(w)`       | An LLVM value that represents a word, i.e. whose region identifier is 0, given a bitvector expression `e:bv w` |
| `x &+ o`                     | `llvmptr(w)`       | An LLVM pointer built by adding an offset `o` (a bitvector expression) to an LLVM pointer variable `x` |
| `R`                          | `rwmodality`       | The read modality |
| `W`                          | `rwmodality`       | The write modality |
| `p`                          | `perm(a)`          | A permission as an expression |

In addition to the above expressions, we also have shape expressions, which we separated out only for the sake of readability.

| Shape Permission Expressions `sh` | Type | Description |
| :---: | :---: | :--- |
| `emptysh`                   | `llvmshape w` | The empty shape |
| `name<e1,..,en>`            | `llvmshape w` | A named shape along with arguments for it, with optional read/write and lifetime modalities that are applied to the body of the shape. Named shapes can either be (1) defined shapes (alias) (2) recursive shapes, or (3) opaque shapes (axioms-all you know is their length). |
| `eqsh(e)`                   | `llvmshape w` | A shape equal to the llvmblock `e`, where `e` is an expression of type `llvmblock w`. Used to type memcpy. |
| `sh1 orsh sh2`              | `llvmshape w` | A disjunctive shape. `sh1` and `sh2` need not have the same size. |
| `sh1 ; sh2`                 | `llvmshape w` | A sequence of two shapes |
| `[l]ptrsh(rw,sh)`           | `llvmshape w` | A shape for a pointer to another memory block, i.e. a memblock permission, with a given shape. This memblock permission will have the same read/write and lifetime modalities as the memblock permission containing this pointer shape, unless they are specifically overridden by the pointer shape; i.e., we have that `[l]memblock(rw,off,len,[l']ptrsh(rw',sh)) = [l]memblock(rw,off,len, fieldsh([l']memblock(rw',0,len(sh),sh)))`, where `rw'` and/or `l'` can be `Nothing`, in which case they default to `rw` and `l`, respectively. |
| `fieldsh(sz,p)`             | `llvmshape w` | A shape for a single pointer field, given a permission `p` that acts on a pointer of size `sz`. |
| `fieldsh(p)`                | `llvmshape w` | Equivalent to `fieldsh(w,p)`. |
| `arraysh(s,len,sh)`         | `llvmshape w` | A shape for an array with the given stride, length (in number of elements = total length / stride), and fields `sh` |
| `exsh x:a.sh`               | `llvmshape w` | An existential shape |
| `falsesh`                    | `llvmshape w` | The unsatisfiable or contradictory shape |


Value permissions
=================

A value permission is a permission to do something with a value, such as use it as a pointer. This also includes a limited set of predicates on values (you can think about this as \"permission to assume the value satisfies this predicate\" if you like).

The type of permissions, `perm(a)`, can be thought of as a function from values of type a to a pair of a proposition and a rely-guarantee permission.

```
[| perm(a) |] = a -> (prop * rely-guarantee permission)
```

For example, informally:

```
[| ptr((W,0) ⊢> true) |] = \x ->
   (x is allocated, you can read/write to *x in
   the current memory and no one else can)

[| ptr((R,0) ⊢> true) |] = \x ->
   (x is allocated, you can read from *x in the current memory
   and no one else can write to it)
```

For a variable `x:a`, the proposition `x:p` means "`x` has permission `p`": this takes `[|p|]:a -> (prop * RG perm)` and applies it to `x:a` to get a `(prop * rg perm)`

| Permissions `p`                           | Type                  | Description  |
| :---: | :---: | :--- |
| `true`                                    | `perm(a)`                 | trivial permission that always holds |
| `p1 or p2`                                | `perm(a)`                 | disjunction; both `p1` and `p2` must satisfy `perm(a)` |
| `p1 * p2`                                 | `perm(a)`                 | separating conjunction; `p1` and `p2` (both satisfying `perm(a)`) must be atomic permissions (not a disjunction, existential, or equality permission) |
| `eq(e)`                                   | `perm(a)`                 | a value equal to the expression `e:a` |
| `exists x:a. p`                           | `perm(b)`                 | there exists some expression `e:a` such that `p[e/x]:perm(b)` holds |
| `false`                           | `perm(a)`  | The unsatisfiable or contradictory permission |
| `x<e1,..,e2>@o`                           | `perm(a)`                 | A named permission with expression arguments, with optional offset expression `o`. Named permissions can either be (1) defined permissions (aliases) (2) recursive permissions, or (3) opaque permissions (axioms). |
| `[l]array(rw, off,<len,*stride,sh)`       | `perm(llvmptr w)`         | a permission for a pointer to an array, where: <ul><li>`l` is the lifetime during which this permission is active;</li> <li>`off` is a permission expression representing the offset of this array from the pointer in bytes;</li> <li>`len` is a permission expression representing the number of cells in the array;</li> <li>`stride` is a permission expression representing the number of bytes in a cell;</li> <li>`sh` is a shape expression representing the shape of elements in the array</li> </ul> |
| `[l]memblock(rw,o,len,sh)`                | `perm(llvmptr w)`         | gives read or write access to a memory block, whose contents also give some permissions, where: <ul> <li> `rw` indicates whether this is a read or write block permission </li> <li> `l` is the lifetime during which this block permission is active </li> <li> `o` is the offset of the block from the pointer in bytes </li> <li> `len` is the length of the block in bytes </li> <li> `sh` is the shape of the block </li> </ul>                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `free(e)`                                 | `perm(llvmptr w)`         | Says that we have permission to free the memory pointed at by this pointer if we have write permission to `e` words of size `w`, where `e` is a permission expression for a bitvector of width `w`.  Superseded by opaque permissions. |
| `[l]ptr((rw,o) \|-> p)`                | `perm(llvmptr w)`         | pointer permission where <ul> <li> `l` is a lifetime during which the permission can be used </li> <li> `rw` is a read or write token </li> <li> `o` is the offset from the variable the permission applies to where the read or write is being allowed  </li> <li> `p` is the permission held by the value being pointed to at the offset, of type `perm(llvmptr w)`. </li> </ul> This is similar to `exists y. [l]ptr((rw,o) ⊢> eq(y)) * y:p` but we can't actually write this in Heapster because we can't write `y:p` on locally-bound variables.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| `[l]ptr((rw,o,sz) \|-> p)`             | `perm(llvmptr w)`         | Similar to `[l]ptr((rw,o) ⊢> p)` but where the value pointed to has `sz` bits, i.e., `p:llvmptr sz`. So, for `x : llvmptr w` (`w` = number of bits), the permission  `[l]ptr((rw,o) ⊢> p)` is equivalent to `[l]ptr((rw,o,w) ⊢> p)`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `shape(sh)`                               | `perm(llvmblock w)`       | Says that a memory block has shape expression `sh`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `lowned [ls](x1:P1,... -o x1':P1',...)` | `perm(l)`          | Permission `l:lowned (...)` says that the current task/process/function/code *owns* lifetime `l`. A lifetime intuitively represents a period of time, during which it is "current" and after which it is "finished". Ownership of `l` is the permission to end `l` whenever you want, assuming certain conditions (described below) are met, along with the knowledge that `l` has not yet been ended, i.e., that `l` is current. This latter knowledge allows the owner of `l` to use permissions like `[l]ptr(...)` that depend on `l` being current. <br> Most of the structure of the lowned permission describes the conditions under which `l` can be ended. The list `ls` contains lifetimes that are contained in `l`, meaning they must end before `l` ends. Once all lifetimes in ls are finished, the act of ending `l` can be performed, and has permission type given by the implication `∏in -o ∏out`, where each `∏` is a list of the form `x1:P1, ..., xn:Pn`. That is, ending `l` requires permissions `∏in` to be "given back" to `l`, and in exchange the ender gets permissions `∏out`, which are intuitively being held by `l` until it is finished. |
| `[l']lcurrent`                           | `perm(l)`          | Assertion that a lifetime `l` is current during another lifetime expression `l'`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `lfinished`                               | `perm(l)`          | Assertion that a lifetime has finished                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `llvmfunptr{n,w}((x0:p_g,...) arg0:p0,... -o arg0:p0',...,ret:p_ret)`  | `perm(llvmptr w)`         | Says an LLVM value is a pointer to a function with `n` arguments, each of which have type `llvmptr w` (i.e., have bit width `w`), and with output type `llvmptr w`. This function takes in ghost arguments `x0:p_g,...`, as well as input permissions given by permission `p0` on the first argument, `p1` on the second, etc.. The function returns permissions `p0'` on the first argument, `p1'` on the second, etc., along with permission pret on the return value. <br> Note that `arg0`, `arg1`, etc, and `ret`, are not variables: they must have those names, though the argument variables may occur in any order.                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
| `llvmframe[e1:m1,..,en:mn]`             | `perm(llvmframe w)`       | Permission to allocate (via `alloca`) on an LLVM stack frame, and permission to delete that stack frame if we have exclusive permissions to all the given LLVM pointer objects. The frame permission is a list of permission expressions (`e_i`) for pointers that have been allocated in the frame and their corresponding allocation sizes (`m_i`) in words of size `n`.                                                                                                                                                                                                               |
| `struct(p1,..,pn)`                        | `perm (struct(a1,..,an))` | A struct permission is a sequence of permissions for each argument of the crucible struct type |
