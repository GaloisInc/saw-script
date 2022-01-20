
# Heapster Developer Documentation

This directory contains an implementation of the Heapster portion of SAW.

## Overall Code Structure

The central components of Heapster are in the following files:

* Permissions.hs: This file defines the language of _permissions_, which are the types in Heapster. Heapster permissions are defined by the `ValuePerm` datatype, which is defined mutually with the type `PermExpr` of Heapster expressions.

* Implication.hs: This file defines the concept of _permission implication_ in Heapster, which is a form of subtyping on the Heapster permission types. Permission implication is defined by the `PermImpl` type, which represents a proof that one permission implies, or is a subtype of, another. This file also contains the implication prover, which is the algorithm that attempts to build permission implication proofs. The implication prover is described in more detail below.

* TypedCrucible.hs: This file defines a version of Crucible control-flow graphs (CFGs) that have been type-checked by Heapster. Each Crucible data type used to define CFGs, including the type `CFG` itself, has a corresponding data type in TypedCrucible.hs with `"Typed"` prefixed to its name. This includes the `TypedCFG` type used to represent an entire typed-checked CFG. This file also contains the function `tcCFG` that performs type-checking on a Crucible CFG, along with helper functions used to type-check the various component pieces of Crucible CFGs.

* SAWTranslation.hs: This file defines the translation from type-checked Crucible CFGs to SAW core terms that represent their specifications.

[comment]: <> (FIXME: describe the other files)


## Heapster Permission Implication

Heapster permission implication is a form of _affine logic_, which in turn is a form of the better-known concept of linear logic. Linear logic is a logic where each proposition assumed by a proof must be used exactly once in that proof. Propositions in linear logic can thus be viewed as a form of "resource" that gets used up in building a proof. For example, consider the rule

```
dollar * dollar * dollar |- candy_bar
```

to represent the concept that a particular candy bar costs $3. Intuitively, the `dollar` proposition represents possession of a dollar, `candy_bar` represents possession of a (reasonably fancy) candy bar, and `*` represents the conjunction of two propositions. A "proof" using this rule consumes three `dollar` propositions and generates one `candy_bar` proposition, intuitively representing the purchase of this candy bar. Importantly, unlike standard classical or even intuitionistic logic, where `P and P` is equivalent to `P`, the conjunction `P * P` in linear logic represents two copies of the proposition `P`, which in general is different than `P` by itself; e.g., if we could prove `dollar |- dollar * dollar` then we could generate all the money we wanted. This is not to say that `P |- P * P` is never true, just that it is only true for some `P`, which correspond to resources that can be duplicated. See any introduction to linear logic for more details.

Affine logic is a version of linear logic where propositions can be "thrown away", that is, where the rule `P * Q |- P` holds for all `P` and `Q`. The reason we use affine logic here is that it is useful for describing a notion of _permissions_, where each `P` intuitively corresponds to permission to perform a particular action. It is always justified to forget some permission if you are not going to use it, but you can't in general give yourself more permissions. One of the central permissions used in Heapster is the permission to access memory through a particular pointer. The simplest form of this is the pointer permission `x:ptr((rw,off) |-> p)`, that represents a permission to read &mdash; and possibly write, depending on `rw` &mdash; memory at offset `off` from `x`, along with permission `y:p` to whatever value `y` is currently stored there. The `array` and `memblock` permissions also represent different forms of permission to read and possibly write memory, with different stipulations on the permissions held for the values currently stored there. Read-only permissions are copyable, meaning that `x:ptr((R,off) |-> p) |- x:ptr((R,off) |-> p) * x:ptr((R,off) |-> p)` can be proved in Heapster, as long as `p` does not contain any write permissions, while write permissions `x:ptr((W,off) |-> p)` are not. This corresponds to the one-writer or multiple readers paradigm of, e.g., Rust.

The remainder of this section explains Heapster implication in more detail and then describes the permission implication prover algorithm used by Heapster used to prove these implications.


### Permission Implication Rules

At any given point during type-checking and/or implication proving, Heapster maintains a _permission set_ that describes the current permissions to various objects that are currently held by the program. Permission sets are defined by the `PermSet` type in Permissions.hs, and have two components: the _permissions map_, which maps each variable `x` in scope to what is called the _primary_ permission held on `x`; and the _permissions stack_, which represents the permissions that are actively being used or manipulated. We write a permission set as:

```
x1 -> Px1 * ... * xm -> Pxm; y1:P1 * ... * yn:Pn
```

The portion before the semicolon represents the permissions map, which maps each `xi` to its primary permission `Pxi`, while the portion after the semicolon represents the permissions stack, containing permissions `y1:P1` through `yn:Pn` in sequence. The final permissions `yn:Pn` is the top of the stack. We often write `PS` for a permission set.

The general form of permission implication is the judgment

```
PS |- (z1_1, ..., z1_k1 . PS1) \/ ... \/ (zn_1, ..., zn_kn . PSn)
```

which says that, starting with permission set `PS` on the left-hand side of the turnstyle `|-`, we can prove one of the permission sets `PSi` on the right-hand side. Each disjunctive case could introduce 0 or more existential variables `zi_1, ..., zi_ki`, which can be used in the corresponding permission set `PSi`. We often omit the permissions map and/or the existential variables when they are not necessary; e.g., we write `PS1 |- PS2` instead of `PS1 |- ( [] . PS2)`. We also tend to omit the permissions map from implications, as permissions maps almost never change; thus, e.g., we might write `x:p |- y:q` instead of `x1 -> Px1 * ... * xm -> Pxm; x:p |- x1 -> Px1 * ... * xm -> Pxm; y:q`.

Permission implication in Heapster is actually a sort of "partial implication". The above-displayed implicaiton judgment in fact says that, if we hvae permission set `PS`, we can _try_ to get one of the permission sets `PSi`, though we can't control which one we get, and we might fail. What this failure means exactly is a little hard to define without going into the details of the translation to SAW core / Coq and relationship between the resulting term and the original program. As one way to understand what failure means here, consider that each permission set `PS` actually describes a set of possible states, one for each substitution of values for all the free variables in `PS`. For some of these states, we can exchange the permissions in `PS` for the permissions in one of the `PSi`, though in some of those states, trying to do this leads to undefined behavior, or at least behavior we are not going to reason about. Another way to think about Heapster implication is to always add an extra disjunction `\/ dunno` to each right-hand side, so an implication `PS |- PS1 \/ ... \/ PSn` becomes `PS |- PS1 \/ ... \/ PSn \/ dunno`, meaning that from permissions `PS` we either can get one of the `PSi` or we get a result that says that we have to give up on modeling the current execution of the program. At a slightly more technical level, failure means means that the translation of a failure is just the `errorM` computation, which, again, doesn't mean that the original computation actually has an error, just that we don't know how to reason about it. Either way, we will simply say "prove" or "implies" below instead of something like "partially prove in some states".

Permission implications are built up from two rules, the identity rule and the step rule. The identity rule is just a proof that `PS |- PS`. The step rule looks like this:

```
PS |-(1) (zs1.PS1) \/ ... \/ (zsn.PSn)
PS1 |- (zs1_1.PS1_1) \/ ... \/ (zs1_k1.PS1_k1)
...
PSm |- (zsm_1.PSm_1) \/ ... \/ (zsm_km.PSm_km)
-----------------------------------------------------
PS |- (zs1_1.PS1_1) \/ ... \/ (zs1_k1.PS1_k1) \/ ... \/ (zsm_1.PSm_1) \/ ... \/ (zsm_km.PSm_km)
```

Intuitively, this says that we can start with an implication and then apply further implications to each of the output permission sets of the original implication, yielding a bigger implication of all of the disjuncts returned by all of the further implications. The notation `|-(1)` denotes a single step of implication, which is built using one of the single-step rules that we describe below. Intuitively, this means that a permission implication can be viewed as a tree, whose leaves are identity rules and whose internal nodes are step rules whose shapes are defined by the single step `|-(1)` implication.

Permission implications are represented in Haskell by the type `PermImpl r ps`. The type variable `ps` is a Haskell datakind that specifies a sequence of Crucible types for the variables and permissions on the stack at the beginning of the proof. For example, the representation of an implication `x1:p1 * ... * xn:pn |- PS1 \/ ... \/ PSn` will have type `PermImpl r (RNil :> t1 :> ... :> tn)` in Haskell, where each `xi` has Crucible type `ti` and each `pi` has the corresponding Crucible type `ValuePermType ti` (which is the type of a permission that applies to an element of type `ti`). The datakind `RNil` is the empty sequence. (The "R" stands for "right-associated list", because the cons operator `:>` adds new list elements on the right instead of the left; this datakind is defined in the Hobbits library, but is identical to the one defined in Data.Parameterized.Ctx.)

In addition to describing the form of an implication, the `PermImpl` representation in Haskell also contains a "result" for each output permission set. That is, permission implications are a form of tree, as described above, and the `PermImpl` type stores results `r1, ..., rn` at each leaf `PS1, ..., PSn` in an implication of `PS |- PS1 \/ ... \/ PSn`. The result type is given by the `r` argument to `PermImpl`, and this type is parameterized by the datakind corresponding to the types of the permissions on the stack at that point. That is, a permission implication `PS |- PS1 \/ ... \/ PSn` will contain elements of type `r ps1` through `r psn`, assuming that each `psi` is the Haskell datakind that represents the stack for each `PSi`. Intuitively, the result does something with the permissions `PSi`. The most common example of this is in the typed representation of functions used in TypedCrucible.hs, where a function can contain a permission implication, using the `TypedImplStmt` constructor, to coerce the permissions it currently holds to some form that is needed to perform an operation. For instance, a `load` instruction requires the permissions currently held by a program to be coerced to a `ptr` permission. Whenever an implication `PS |- PS1 \/ ... \/ PSn` occurs in a typed Crucible representation, the remaining instructions must be type-checked relative to each of the permission sets `PSi`. This is represented by having the `PermImpl` representation contain one copy of the remaining instructions for each output `PSi`, type-checked relative to that permission set.

The one-step implication rules defined by the `|-(1)` judgment are defined by the `PermImpl1 ps_in ps_outs` type, which represents a rule with input stack described by datakind `ps_in` and 0 or more disjunctive output stacks given by `ps_outs`, which is a list of 0 or more disjuncts that bind 0 or more existential variables and leave 0 or more types on the stack. (See the documentation of `PermImpl1` for more details.) These include the following rules (along with a few more that we do not discuss here):

| Rule name | Rule description | Rule implication |
----------|-------------|-----------------|
| `Impl1_Fail` | Failure of implication | `ps \|-(1) empty` (where `empty` is 0 disjuncts) |
| `Impl1_Catch` | Try one implication and then a second if the first fails | `ps \|-(1) ps \/ ps` |
| `Impl1_Push` | Push the primary permission for `x` onto the stack | `..., x -> p; ps \|-(1) ..., x -> true; ps * x:p` |
| `Impl1_Pop` | Pop the top of the stack back to the primary permission for `x` | `..., x -> true; ps * x:p \|-(1) ..., x -> p; ps` |
| `Impl1_ElimOr` | Eliminate a disjunction on the top of the stack | `ps * x:(p1 or p2) \|-(1) (ps * x:p1) \/ (ps * x:p2)` |
| `Impl1_ElimExists` | Eliminate an existential on the top of the stack | `ps * x:(exists z.p) \|-(1) (z. ps * x:p)` |
| `Impl1_Simpl` | Apply a simple implication of the form `ps1 \|- ps2` | `ps * ps1 \|-(1) ps * ps2` |
| `Impl1_ElimLLVMFieldContents` | Extract the contents of an LLVM pointer permission | `ps * x:ptr((rw,off) -> p) \|-(1) y. ps * x:ptr((rw,off) -> eq(y)) * y:p` |

[comment]: <> (FIXME: explain the above rules!)

The most common implication rule is `Impl1_Simpl`, which applies a "simple" implication rule that exactly only one disjunctive output permission and binds no variables. The simple implication rules are described by the type `SimplImpl ps_in ps_out`. A rule of this type assumes that permissions `ps_in` are on the top of the stack, though there can be more permissions below these on the stack. It then consumes `ps_in`, replacing them with permissions `ps_out`. (As above, the `ps_in` and `ps_out` type arguments in Haskell are actually datakinds capturing the types of the input and output permissions of the rule.) These include too many rules to list here, so we only describe enough of them to give a flavor of what they do.

Some of the simple implication rules are structural. These include the following:

| Rule name | Rule description | Rule implication |
----------|-------------|-----------------|
| `SImpl_Drop` | Drop a permission | `x:p \|- .` |
| `SImpl_Copy` | Copy any permission that is copyable, i.e., satisfies `permIsCopyable` | `x:p \|- x:p * x:p` |
| `SImpl_Swap` | Swap the top two permissions on the stack | `x:p1 * y:p2 \|- y:p2 * x:p1` |
| `SImpl_MoveUp` | Move a permission towards the top of the stack | `x:p * ps1 * ps2 \|- ps1 * x:p * ps2` |
| `SImpl_MoveDown` | Move a permission away from the top of the stack | `ps1 * x:p * ps2 \|- x:p * ps1 * ps2` |
| `SImpl_IntroConj` | Prove an empty conjunction (which is the same as `true`) | `. \|- x:true` |
| `SImpl_ExtractConj` | Extract the `i`th conjunct of a conjunction | `x:(p0 * ... * p(n-1)) \|- x:pi * x:(p0 * ... p(i-1) * p(i+1) ... * p(n-1))` |
| `SImpl_CopyConj` | Copy the `i`th conjunct of a conjunction, assuming it is copyable | `x:(p0 * ... * p (n-1)) \|- x:pi * x:(p0 * ... * p(n-1))` |
| `SImpl_InsertConj` | Insert a permission into a conjunction | `x:p * x:(p0 * ... * p(n-1)) \|- x:(p0 * ... * p(i-1) * p * pi * ... * p(n-1))` |
| `SImpl_AppendConjs` | Combine the top two conjunctions on the stack | `x:(p1 * ... * pi) * x:(pi+1 * ... * pn) \|- x:(p1 * ... * pn)` |
| `SImpl_SplitConjs` | Split the conjunctive permissions on the top of the stack in two | `x:(p1 * ... * pn) \|- x:(p1 * ... * pi) * x:(pi+1 * ... * pn)` |


The elimination rules for disjunctions and existentials are `PermImpl1`s, because the former has multiple disjuncts and the latter introduces local variables, but their introduction rules are simple implications, as are both the introduction and elimination rules for named permissions:

| Rule name | Rule description | Rule implication |
----------|-------------|-----------------|
| `SImpl_IntroOrL` | Prove a disjunctive permission from its left disjunct | `x:p1 \|- x:(p1 or p2)` |
| `SImpl_IntroOrR` | Prove a disjunctive permission from its right disjunct | `x:p2 \|- x:(p1 or p2)` |
| `SImpl_IntroExists` | Prove an existential permission from a substitution instance | `x:[e/z]p \|- x:(exists z.p)` |
| `SImpl_FoldNamed` | Prove a named permission from its unfolding | `x:(unfold P args) \|- x:P<args>` |
| `SImpl_UnfoldNamed` | Eliminate a named permission by unfolding it | `x:P<args> \|- x:(unfold P args)` |


Equality permissions are manipulated with the following simple implication rules:

| Rule name | Rule description | Rule implication |
----------|-------------|-----------------|
| `SImpl_IntroEqRefl` | Prove any `x` equals itself | `. \|- x:eq(x)` |
| `SImpl_InvertEq` | Prove if `x` equals `y` then `y` equals `x` | `x:eq(y) \|- y:eq(x)` |
| `SImpl_InvTransEq` | Prove that if `x` and `y` equal the same `e` then they equal each other | `x:eq(e) * y:eq(e) \|- x:eq(y)` |
| `SImpl_LLVMWordEq` | If `y` equals `e` then `llvmword(y)` equals `llvmword(e)` | `x:eq(llvmword(y)) * y:eq(e) \|- x:eq(llvmword(e))` |
| `SImpl_LLVMOffsetZeroEq` | Offsetting an LLVM value by `0` preserves equality | `. \|- x:eq(x &+ 0)` |
| `SImpl_InvertLLVMOffsetEq` | Subtract an offset from both sides of an LLVM value equality | `x:eq(y+off) \|- y:eq(x-off)` |
| `SImpl_Cast` | Cast the variable of a permission using an equality | `x:eq(y) * y:p \|- x:p` |
| `SImpl_CastPerm` | Cast a permission `p` to `p'`, assuming that `x1=e1`, ..., `xn=en` imply that `p=p'` | `x1:eq(e1) * ... * xn:eq(en) * x:p \|- x:p'` |



- Implementation of the rules: `simplImplIn` and `simplImplOut`, `applyImpl1`: these all check for correct perms

- Explain overall pattern of the simplimpl rules: intro vs elim rules for most constructs


### The Implication Prover Algorithm

The goal of the implication prover is to search for a permission implication proof using the implication rules discussed above. The implication prover is not complete, however, meaning that there are proofs that can be made with the implication rules that the implication prover will not find. To date, work on the implication prover has focused on heuristics to make it work in practice on code that comes up in practice.

#### The Implication Prover Monad

The implication prover runs in the `ImplM` monad, whose type parameters are as follows:

```
ImplM vars s r ps_out ps_in a
```

An element of this type is an implication prover computation with return type `a`. The type variable `vars` lists the types of the existential variables, or _evars_, in scope. These represent "holes" in the permissions we are trying to prove. The type variables `s` and `r` describe the calling context of this implication computation at the top level: `s` describes the monadic state maintained by this calling context, while `r` describes the top-level result type required by this context. These types are left abstract in all of the implication prover.

The type variables `ps_in` and `ps_out` describe the permission stack on the beginning and end of the computation. The existence of these two variables make `ImplM` a _generalized_ monad instead of just a standard monad, which means that these types can vary throughout an implication computation. The bind for `ImplM` is written `>>>=` instead of `>>=`, and has type

```
(>>>=) :: ImplM vars s r ps' ps_in a -> (a -> ImplM vars s r ps_out ps' b) -> ImplM vars s r ps_out ps_in b
```

That is, the bind `m >>>= f` first runs `m`, which changes the permissions stack from `ps_in` to `ps'`, and then it passes the output of `m` to `f`, which changes the permissions stack from `ps'` to `s_out`, so the overall computation changes the permissions stack from `ps_in` to `ps_out`. As a more concrete example, the computation for pushing a permission onto the top of the stack is declared as

```
implPushM :: HasCallStack => NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
             ImplM vars s r (ps :> a) ps ()
```

meaning that `implPushM` takes in a variable `x` and a permission `p` and returns a computation that starts in any permission stack `ps` and pushes permission `x:p` of type `a` onto the top of the stack.

FIXME HERE: explain that ImplM is a state-continuation monad, whose final output is always a `PermImpl`


#### Needed and Determined Variables

One difficulty in doing proof search which must be addressed by the implication prover is that existential variables mean we do not have most general types. (There are other ways in which Heapster does not have most general types, but this is a more aggregious one.) For instance, there are two distinct ways to prove

```
x:ptr((R,0) |-> true) * x:ptr((R,8) |-> true) |- exists off:bv 64. x:ptr((R,off) |-> true)
```

by instantiating `off` to either 0 or 8. The difficulty is that if we choose the wrong value for `off` we might have to backtrack, potentially leading to an exponential search. The same problem occurs for function permissions with ghost variables, as ghost variables become existential variables that must be instantiated at call sites. Thus, for instance, Heapster cannot handle a function with permissions like

```
(off:bv 64). arg0:ptr((R,off) |-> true) -o empty
```

because it will not know how to instantiate `off` at the call site. Currently, this shows up as a type-checking error when such a function is called, but we could consider raising an error where such a function is defined. If you think about it, though, a function type like this does not really make any sense. How could a function take in a pointer to something where it doesn't know the offset of that pointer?

If, however, there is some other permission that _determines_ the offset, then this problem is resolved. Consider, for instance, the following function type:

```
(off:bv 64). arg0:ptr((R,off) |-> true), arg1:eq(llvmword(off)) -o empty
```

This describes a function whose second argument says what the offset is for the first. Unlike the previous example, Heapster can handle this function type, because it will prove the equality permission on `arg1` first, and this proof will determine the value of `off` to be used for the permission on `arg0`. This function type also makes a lot more sense operationally, because now the function can know what the offset is. The more common version of this situation is passing the length of an array, using a type like this:

```
(len:bv 64). arg0:array(W,0,<len,*1,int8<>), arg1:eq(llvmword(len)) -o empty
```

A similar pattern can occur inside data structures. A common pattern in C is to have a `struct` with a variable-length array at the end, whose length is determined by one of the fields, like this:

```
struct foo {
 ...;
 int64_t len;
 char data[];
}
```

Rust slices are similar. A struct like this can be described by the Heapster shape

```
...; exsh len:bv 64.(fieldsh(eq(llvmword len));arraysh(<len,*1,fieldsh(int8<>)))
```

This shape can be proved by the Heapster implication prover because the existential variable `len` in the shape is determined by the equality permission in the `len` field in the struct. If the struct did not have this field, Heapster would not be able to prove permissions with this shape. Again, such a shape does not really make sense, as the program would never know how long the `data` field is.


The Heapster implication prover addresses the problem of existential variables leading to non-unique types by requiring that all existential variables that could lead to this sort of problem in a permission `p` are assigned a uniquely determined value before it attempts to satisfy permission `p`. These variables are called the _needed_ variables of `p`, defined by the `neededVars` function in Permissions.hs. The needed variables include any free variables in the offsets and lengths of pointer, array, and block permissions, as well as any free variables of the more complicated permissions like lifetime ownership permissions. For equality permissions `eq(e)`, the free variables of `e` are not needed if `e` is a _determining_ expression, discussed below. In our example above, `off` is a needed variable on the right-hand side, so the implication prover will not prove this implication but will instead raise a type-checking error (with the `Impl1_Fail` rule described above).

The only way to prove a permission with needed variables is if there is some other permission which is proved first that _determines_ the value of that variable. Intuitively, the idea is that a permission `p` determines an existential variable `x` if there is only one possible value of `x` for which `p` can possibly be proved. The canonical example of determination is the permission `eq(x)`: the only possible way to prove an `eq(x)` permission is to set `x` to the value that has this permission. If we are proving `y:eq(x)`, then `x` has to be set to `y`, while if we are proving a pointer permission `y:ptr((rw,off) |-> eq(x))`, `x` has to be set to the value pointed to by `y` at offset `off`. Note that, in this latter case, the implication prover will first prove some permission of the form `y:ptr((rw,off) |-> p)` and will then use the `Impl1_ElimLLVMFieldContents` rule to bind a local variable `z` for the value pointed to by `y` at offset `off`, so `x` will be set to this local variable `z`. In order to prove a pointer permission, however, the free variables in `off` (if there are any) must already be determined by some other permission, because these are needed variables of the pointer permission. Thus determined variables have a dependency structure, where some variables can only be determined if other variables are determined first. Further, a variable can not be determined by an equality inside an arbitrary permission. For instance, `eq(x) or p` does not determine `x`, because the proof may not take the left-hand branch of the disjunct.

More generally, determined variables are defined by the `determinedVars` function. This function uses the helper function `isDeterminingExpr` to define whether an expression `e` used in an equality permission determines its variables. The following expression forms are determining:
* `x`
* `llvmword e` if `e` is determining
* `N*x + K` for constants `N` and `K`
* The permission `eq(e)` as an expression if `e` is determining
* `x &+ off` if `off` is determining
* Any expression with no free variables

The `determinedVars` function is then defined as follows on permission `p`:

| Permission `p` | Determined Variables |
|-------------|----------------------|
| `eq(e)` | The free variables of `e` if `e` is a determining expression, otherwise `[]` |
| `p1 * ... * pn` | The determined variables of the `pi` |
| `P<args>` | The free variables of each determining expression in `args` |
| `[l]ptr((rw,off) |-> p)` | The determined variables of `l`, `rw`, and `p`, if the variables in `off` are determined |
| `[l]array(rw,off,<len,*stride,sh,bs)` | The determined variables of `l`, `rw`, and `sh`, if the variables in `off`, `len`, and `bs` are determined |
| `[l]memblock(rw,off,len,sh)` | The determined variables of `l`, `rw`, and `sh`, if the variables in `off` and `len` are determined |
| `llvmframe[e1:i1, ..., en:in]` | The free variables of each `ei` that is a determining expression |



#### The Top-Level Implication Prover Algorithm

The main top-level entrypoints of the implication prover is `proveVarsImplAppend`, with type

```
proveVarsImplAppend :: Mb vars (DistPerms ps) -> ImplM vars s r (ps_in :++: ps) ps_in ()
```

This function attempts to prove `n` permisisons `x1:p1, ..., xn:pn`, adding those permissions to the top of the permissions stack. These permissions are inside of a binding for the existential variables specified by `vars`, which represent "holes" or unknown expressions that will be solved by building the proof. As an example, the type-checker for the pointer read instruction calls the implication prover with the existentially quantified permission

```
(rw,l,z). [l]ptr((rw,0) |-> eq(z))
```

expressing that it requires a pointer permission at offset 0 with any lifetime `l`, any read/write modality `rw`, that points to any value `z`.

There are a number of wrapper functions that call `proveVarsImplAppend`, including:

* `proveVarsImpl`, which assumes the input permission stack is empty;
* `proveVarImpl`, which proves one permission; and
* `proveVarsImplVarEVars`, which is like `proveVarsImpl` but where all existential variables are instantiated with fresh variables.

The top-level implication prover algorithm is then implemented as a descending sequence of "levels", each of is implemented as a function that performs some particular function and then calls the next level:

| Function Name | Purpose |
--------------|----------|
| `proveVarsImplAppend` | Try to prove the required permissions, and, if that failos, non-deterministically end some lifetimes that could help in the proof |
| `proveVarsImplAppendInt` | Repeatedly call `findProvablePerm` to find the permission on the right that is most likely to be provable and then try to prove that permission |
| `proveExVarImpl` | Handle the case of a right-hand permission `x:p` where `x` itself is an evar by instantiating `x`, if possible |
| `proveVarImplInt` | Wrapper function that pushes the primary permissions for `x` onto the top of the stack, performs debug tracing, calls `proveVarImplH`, and then checks that the proved permission is correct |


#### Proving a Permission

The main logic for proving a permission is in the function `proveVarImplH`. (The implication prover uses the convention of using "`H`" as a suffix for helper functions.) As with many functions in the implication prover, this function takes in: a variable `x` that we are trying to prove a permission on; a permission `p` for `x` which is currently on top of the stack; and a permission `mb_p` inside a context of evars that we are trying to prove for `x`. (The prefix "`mb`" refers to "multi-binding", a binding of 0 or more evars.) The function then works by pattern-matching on `p` (the left-hand side) and `mb_p` (the right-hand side), using the following cases, some of which call out to helper functions described below:

| Left-hand side | Right-hand side | Algorithmic steps taken |
|------------|--------------|--------------------|
| `p` | `true` | Pop `p` and Introduce a vacuous proof of `true` |
| `p` | `eq(e)` | Call `proveVarEq` to prove the equality |
| `p1 or p2` | `mb_p` | Eliminate the disjunction and recurse |
| `exists z. p` | `mb_p` | Eliminate the existential and recurse |
| `eq(y)` | `mb_p` | Prove `y:mb_p` and then cast the proof to `x:mb_p` |
| `eq(y &+ off)` | `mb_p` | Prove `y:(offsetPerm mb_p off)` and then case the proof to `x:mb_p` |
| `p` | `mb_p1 or mb_p2` | Nondeterminsitically try to prove either `mb_p1` or `mb_p2` |
| `p` | `exists z. mb_p` | Add a new evar for `z`, prove `x:mb_p`, and then use the value determined for `x` to introduce an existential permission |
| `P<args>` | `mb_p` | Use the more specific rules below for named permissions |
| `p1 * ... * pi-1 * P<args> * pi+1 * ... * pn` | `mb_p` | Use the more specific rules below for named permissions |
| `p` | `P<mb_args>` | Use the more specific rules below for named permissions |
| `eq(llvmword e)` | `p1 * ... * pn` | Fail, because we cannot prove any non-equality permissions for words, and the equality permissions were matched by an earlier case |
| `eq(struct(e1,...,en))` | `mb_p` | Eliminate `eq(struct(e1,...,en))` to a `struct(eq(e1),...,eq(en))` permission with equalities for each field |
| `eq(constant f)` | `(gs) ps_in -o ps_out` | Use an assumption on known function `f` |
| `p1 * ... * pn` | `mb_p1 * ... * mb_pn` | Call `proveVarConjImpl` to prove a conjunction implies a conjunction |
| `p` | `(X). X` | For existential permission variable `X`, set `X:=p` |
| `X` | `X` | For universal permission variable `X`, prove `X -o X` by reflexivity |
| `_` | `_` | In all other cases, fail |


#### Proving Named Permissions

| Left-hand side | Right-hand side | Algorithmic steps taken |
|------------|--------------|--------------------|
| `P<args,e>` | `P<mb_args,mb_e>` | For reachabilitiy permission `P`, nondeterministically prove the RHS by either reflexivity, meaning `x:eq(mb_e)`, or transitivity, meaning `e:P<mb_args,mb_e>` |
| `P<args>` | `P<mb_args>` | For non-reachabilitiy named permission `P`, prove `args` _weakens to_ `mb_args`, where write modalities weaken to read, bigger lifetimes weaken to smaller ones, and otherwise arguments weaken to themselves |
| `p1 * ... * pi-1 * P<args> * pi+1 * ... pn` | `P<mb_args>` | Similar to above |
| `p` | `P<mb_args>` | If `P` is a _defined_ (i.e., non-recursive) name, unfold `P` to its definition and recurse |
| `P<args>` | `mb_p` | If `P` is a defined name, unfold `P` to its definition and recurse |
| `p1 * ... * pi-1 * P<args> * pi+1 * ... pn` | `mb_p` | If `P` is defined, unfold `P` to its definition and recurse |
| `P1<args>` | `P2<mb_args>` | If `P1` and `P2` are both recursively-defined, nondeterminstically choose one side to unfold |
| `p1 * ... * pi-1 * P1<args> * pi+1 * ... pn` | `P2<mb_args>` | If `P1` and `P2` are both recursively-defined, nondeterminstically choose one side to unfold |
| `p` | `P<mb_args>` | If `P` is recursive, unfold `P` and recurse |
| `P<args>` | `mb_p` | If `P1` and `P2` are both recursively-defined, nondeterminstically choose 

FIXME HERE: mention the recursion flag: cannot unfold on the left and the right in the same proof


#### Proving Equalities and Equality Permissions

FIXME HERE:
- Explain the representaiton of equality proofs
- `proveEq` builds an equality proof
- `proveVarEq` then casts a reflexive equality proof `x:eq(x)` to one of `x:eq(e)` using a proof of `x=e`


#### Proving Conjuncts of Permissions

FIXME HERE:
- Explain that `proveVarConjImpl` repeatedly chooses the "best" permission to prove next; chooses defined permissions first, then recursive ones, then those whose needed vars are determined
- give the table of cases


#### Proving Field Permissions

#### Proving Array Permissions

#### Proving Block Permissions


## Crucible Type-checker

FIXME

## SAW Translator

FIXME