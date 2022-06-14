
# The Heapster Implication Prover

This document describes the Heapster implication prover.

## The Implication Prover Monad

The implication prover runs in the `ImplM` monad, whose type parameters are as follows:

```
ImplM vars s r ps_out ps_in a
```

An element of this type is an implication prover computation with return type `a`. The type variable `vars` lists the types of the existential variables, or _evars_, in scope. These represent "holes" in the permissions we are trying to prove. The type variables `s` and `r` describe the calling context of this implication computation at the top level: `s` describes the monadic state maintained by this calling context, while `r` describes the top-level result type required by this context. These types are left abstract in all of the implication prover.

The type variables `ps_in` and `ps_out` describe the permission stack on the beginning and end of the computation. The existence of these two variables make `ImplM` a _generalized_ monad instead of just a standard monad, which means that these types can vary throughout an implication computation. The bind for `ImplM` is written `>>>=` instead of `>>=`, and has type

```
(>>>=) :: ImplM vars s r ps' ps_in a -> (a -> ImplM vars s r ps_out ps' b) ->
          ImplM vars s r ps_out ps_in b
```

That is, the bind `m >>>= f` first runs `m`, which changes the permissions stack from `ps_in` to `ps'`, and then it passes the output of `m` to `f`, which changes the permissions stack from `ps'` to `s_out`, so the overall computation changes the permissions stack from `ps_in` to `ps_out`. As a more concrete example, the computation for pushing a permission onto the top of the stack is declared as

```
implPushM :: HasCallStack => NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
             ImplM vars s r (ps :> a) ps ()
```

meaning that `implPushM` takes in a variable `x` and a permission `p` and returns a computation that starts in any permission stack `ps` and pushes permission `x:p` of type `a` onto the top of the stack.

If the permission stack does not change, meaning that `ps_in` equals `ps_out`, then `ImplM` forms a monad. For instance, the function

```
partialSubstForceM :: (NuMatchingAny1 r, PermPretty a,
                       Substable PartialSubst a Maybe) =>
                      Mb vars a -> String -> ImplM vars s r ps ps a
```

takes the current partial substitution for the evars and attempts to apply it to a value in a name-binding for those evars, raising an error if some evar that has not yet been instantiated is used in the value. (The "force" means to force the substitution to be defined or fail.) This function does not change the permission stack, and is in fact written in `do` notation in the code.

The `ImplM` monad is defined as a generalized state-continuation monad. This construct is defined in `GenMonad.hs`, but we will not discuss it in too much detail here. The state that is maintained is given by the `ImplState` type, which contains information such as the current permission set, the types of all univeral and existential variables in scope, and the current instantiations of all the evars. The input and output types of the continuation portion of `ImplM` are both `PermImpl`, meaning each `ImplM` computation builds up an implication. The fact that `ImplM` is a continuation monad is only used in the `implApplyImpl1` function, which applies an `Impl1` rule by shifting the current continuation and re-applying it to build the sub-`PermImpl`s passed to that rule as an `MbPermImpls`. This means that rules with multiple disjunctive outputs, like or elimination and the catch rule, cause `ImplM` to fork its execution, running any subsequent computation once in each disjunctive branch. Thus, for performance reasons, it is helpful to reduce this forking as much as possible.


## Needed and Determined Variables

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
| `[l]ptr((rw,off) \|-> p)` | The determined variables of `l`, `rw`, and `p`, if the variables in `off` are determined |
| `[l]array(rw,off,<len,*stride,sh,bs)` | The determined variables of `l`, `rw`, and `sh`, if the variables in `off`, `len`, and `bs` are determined |
| `[l]memblock(rw,off,len,sh)` | The determined variables of `l`, `rw`, and `sh`, if the variables in `off` and `len` are determined |
| `llvmframe[e1:i1, ..., en:in]` | The free variables of each `ei` that is a determining expression |


## Recombining Permissions

FIXME HERE: explain `recombinePerm`


## The Top-Level Implication Prover Algorithm

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


## Proving a Permission

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


## Proving Named Permissions

Named permissions are of the form `P<args>` for some permission name `P`. Each named permission represents some more complicated collection of permissions, that can depend on the argument expressions `args`. Permission names come in three sorts:

* _Defined names_ are essentially abbreviations, where `P<args>` unfolds to some permission `p` that does not contain `P` itself (unless `P` occurs `args`);

* _Recursive names_ `P` are similar to defined names but where `P<args>` unfolds to a permission that can contain `P`; and

* _Opaque names_ are permissions which are too complicated to represent in Heapster, so Heapster just represents them with names.

The "best" way to prove a named permission `P<args>` is by reflexivity, i.e., to find an instance of `P<args>` that is already in the current permissions set. The implication rules do allow some amount of weakening the arguments, so technically this is a search for `P<args'>` for some argument list `args'` that can be coerced to `args`. For opaque names, this is the only way to prove `P<args>`. For defined names, the other option is to just unfold `P<args>` to its definition, prove that permission, and then fold the result to `P<args>`. Similarly, recursive names can also be unfolded to prove them. Dually, if there is a permission `P<args>` with a defined or recursive name on the left, meaning it is already held in the current permission set, the implication prover will unfold this permission if it gets stuck trying to prove its goal any other way. This logic is implemented by the `implUnfoldOrFail` function, which is called in a number of places in the implication prover where it will otherwise fail.

The one wrinkle is that unfolding recursive names can lead to non-termination. This can happen if we have an assumption `P1<args1>` on the left and we are trying to prove `P2<args2>` on the right where both `P1` and `P2` are recursive names. If we proceed by unfolding both `P1` and `P2`, then, because these unfoldings can each contain `P1` and `P2` again, we can end up back at the same proof goal, of having an assumption `P1<args1>` on the left and trying to prove `P2<args2>`. To prevent this infinite regress, the implication prover is restricted so that it will not unfold names on both the left and right sides in the same proof. This is done by maintainining a flag called `implStateRecRecurseFlag` that tracks whether there has been an unfolding of a recursive name on one side or the other. Whenever the implication prover has `P1<args1>` on the left and `P2<args2>` on the right for recursive names `P1` and `P2`, it then non-deterministically (using the `Impl1_Catch` rule to backtrack) chooses one side to unfold, and it proceeds from there. This handles the possibility that one of `P1` or `P2` contains the other as a sub-permission.

In more detail, here are the cases of `proveVarImplH` that handle recursive permissions:

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


## Proving Equalities and Equality Permissions

Equality permissions are proved by `proveVarEq`, which takes a variable `x` and an expresson `mb_e` in a binding of the existential variables, and proves `x:eq(e)` for some instantiation `e` of the variables in `mb_e`. This function pushes a reflexive proof that `x:eq(x)`, calls `proveEq` to build an equality proof that `x=e`, and uses the equality proof with the `SImpl_CastPerm` rule to cast the proof of `x:eq(x)` on top of the stack to `x:eq(e)`. The meat of `proveVarEq` is thus in `proveEq`, which attempts to build equality proofs. The `proveEq` function is also called in other parts of the implication prover, e.g., to coerce the modalities of field, array, and block permissions.

An equality proof in Heapster is a transitive sequence of equality proof steps `e=e',e'=e'',...`. Each step is a sequence of equality permissions `x1:eq(e1),...,xn:eq(en)`, where each equality `xi:eq(ei)` is oriented either left-to-right as `xi=ei` or right-to-left as `ei=xi`, along with a function `f` on `n` expressions. This represents the equality `f(left1,...,leftn)=f(right1,...,rightn)`, where `lefti` and `righti` are the left- and right-hand sides of the `i`th oriented version `xi=ei` or `ei=xi` of the permission `xi:eq(ei)`. Equality steps are represented by the Haskell type `EqProofStep ps a`, where `ps` is a list of the types of the variables `x1,...,xn` and `a` is the Haskell type of the objects being proved equal. (Equality proofs can be used not just on expressions, but at other types as well.) Entire equality proofs are represented by the type `EqProof ps a`, while the type `SomeEqProof a` is an equality proof where the permissions needed to prove it are existentially quantified.

[comment]: <> (FIXME HERE: describe `proveEq` and `proveEqH`)


## Proving Conjuncts of Permissions

Conjuncts `p1 * ... * pn` are proved by `proveVarConjImpl`, which repeatedly picks the "best" permission on the right to prove and calls `proveVarAtomicImpl` to prove it. Finding the "best" permission prioritizes defined permissions first, followed by recursive permissions, as this fits with the named permissions algorithm described above, followed by finding a permission whose needed variables have all been determined.

The cases for `proveVarAtomicImpl` are as follows:

| Permission to prove | Algorithmic steps taken |
|----------------|--------------------|
| `[l]ptr((rw,off) \|-> p)` | Call `proveVarLLVMField` |
| `[l]array(rw,off,<len,*stride,sh,bs)` | Call `proveVarLLVMArray` |
| `[l]memblock(rw,off,len,sh)` | Call `proveVarLLVMBlock` |
| `free(e)` | If there is a `free(e')` permission on the left, cast it to `free(e)` by proving `e'=e` |
| `llvmfunptr(...)` | If there is an identical `llvmfunptr(...)` permission on the left, use it |
| `is_llvmptr` | If there is an `is_llvmptr`, field, array, or block permission, use it (with the corresponding implication rule in the latter cases) to prove that the variable is a pointer |
| `shape(sh)` | If there is a `shape(sh')` permission on the left, cast it to `shape(sh)` by proving `sh'=sh` |
| `llvmframe[e1:i1,...,en:in]` | If there is an `llvmframe` permission on the left, cast it to the required permission |
| `lowned[](ps_in -o ps_out)` | If there is an `lowned[ls](ps_in' -o ps_out')` permission on the left with `ls!=[]`, end the lifetimes in `ls` using `implEndLifetimeRecM` |
| `lowned[](ps_in -o ps_out)` | If there is an `lowned[](ps_in' -o ps_out')` permission on the left, prove that `p1 * ps_in' -o ps_in` and `p2 * ps_out -o ps_out'` for some `p1` and `p2`, by calling `solveForPermListImpl` to solve for `p1` and `p2`, and then use these proofs with the `SImpl_MapLifetime` rule |
| `l:[l']lcurrent` | Build the proof by taking the reflexive-transitive closure of any `lcurrent` and `lowned` permissions on the left, noting that `l:lowned[ls](ps_in -o ps_out)` implies `l:[li]lcurrent` for any `li` in the `ls` list |
| `l:lfinished` | End lifetime `l` by calling `implEndLifetimeRecM` |
| `struct(p1,...,pn)` | If we have `struct(q1,...,qn)` on the left, eliminate each field to a fresh variable using the `Impl1_ElimStructField` rule, yielding permission `struct(eq(x1),...,eq(xn))` along with permissions `x1:q1,...,xn:qn`, and then prove `x1:p1,...,xn:pn` and introduce them into the required struct permission |
| `(xs).ps_in -o ps_out` | If the identical permission `(xs).ps_in -o ps_out` is on the left, use it |
| `_` | In all other cases, call `proveVarAtomicImplUnfoldOrFail` to unfold any names on the left to try to make more progress, or fail if this is not possible |


## Proving Field Permissions

To prove a field permission `[l]ptr((rw,off) |-> p)`, the `proveVarLLVMField` function starts by first calling `implGetLLVMPermForOffset` to find a permission on the left that contains `off`. If this permission is a `memblock` permission, it is repeatedly eliminated, using the helper function `implElimLLVMBlock`, until an array or field permission is obtained. This permission is then passed to `proveVarLLVMFieldH`, which calls `proveVarLLVMFieldH2`, which dispatches based on the form of the permission. We call this the left-hand permission in this discussion, since `implGetLLVMPermForOffset` puts it on the top of the stack, i.e., the left of the implication.

The main case `proveVarLLVMFieldH2` is when the left-hand permission is a field permission
`[l']ptr((rw',off) |-> p')` of the same size as the required one. In this case, `proveVarLLVMFieldH2` performs the following steps:
* Eliminate the contents of the field permission to get a permission of the form `[l']ptr((rw',off) |-> eq(y))` for some variable `y`;
* Prove `y:p` with a recursive call to `proveVarImplInt`;
* Use the `SImpl_IntroLLVMFieldContents` to combine the `y:p` permission into the left-hand permission to get `[l']ptr((rw',off) |-> p)`;
* Coerce the lifetime `l'` to `l` by calling `proveVarLifetimeFunctor`, which splits or ends lifetimes as needed;
* Coerce `rw'` to `rw` by calling `equalizeRWs`, which either proves the two are equal using `proveEq` and casting or weakens a write modality to a read modality; and
* Duplicate and recombine the pointer permission if it is copyable.

If the left-hand permission is a pointer permission that is bigger than required, split the left-hand permission by calling `implLLVMFieldSplit`, recombine the part that is not required, and recursively call `proveVarLLVMFieldH` with the remaining left-hand permission.

If the left-hand permission is a pointer permission that is smaller than required:
* Recursively call `proveVarLLVMFieldH` with the same left-hand permission to prove a pointer permission `[l]ptr((rw,off) |-> eq(y))` of the same size, i.e., with existential variable `y:llvmptr (8*sz)` where `sz` is the size of the left-hand permission in bytes;
* Prove `[l]ptr((rw,off+sz) |-> eq(z))` for existential variables `z` of the remaining size;
* Call `implLLVMFieldConcat` to concatenate these two field permissions; and
* Call `proveVarLLVMFieldH` with the resulting permission of the correct size as the left-hand permission.

If the left-hand permission is an array permission where the required permission lines up with one of the cells of the array, borrow or copy (depending on whether the array is copyable) the corresponding array cell and recursively call `proveVarLLVMFieldH` with the cell permission that was borrowed.

If the left-hand permission is an array permission where the required permission covers multiple cells of the array, borrow or copy those cells (depending on whether the array is copyable) as a single array permission, coerce the resulting cells to a field using the `SImpl_LLVMArrayToField` rule, and pass the resulting permission as the left-hand permission of a recursive call to `proveVarLLVMFieldH`.

In all other cases, `proveVarLLVMFieldH2` fails.


## Proving Array Permissions



## Proving Block Permissions

