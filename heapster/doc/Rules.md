# Heapster Permission Implication

Heapster permission implication is a form of _affine logic_, which in turn is a form of the better-known concept of linear logic. Linear logic is a logic where each proposition assumed by a proof must be used exactly once in that proof. Propositions in linear logic can thus be viewed as a form of "resource" that gets used up in building a proof. For example, consider the rule

```
dollar * dollar * dollar |- candy_bar
```

to represent the concept that a particular candy bar costs $3. Intuitively, the `dollar` proposition represents possession of a dollar, `candy_bar` represents possession of a (reasonably fancy) candy bar, and `*` represents the conjunction of two propositions. A "proof" using this rule consumes three `dollar` propositions and generates one `candy_bar` proposition, intuitively representing the purchase of this candy bar. Importantly, unlike standard classical or even intuitionistic logic, where `p and p` is equivalent to `p`, the conjunction `p * p` in linear logic represents two copies of the proposition `p`, which in general is different than `p` by itself; e.g., if we could prove `dollar |- dollar * dollar` then we could generate all the money we wanted. This is not to say that `p |- p * p` is never true, just that it is only true for some `p`, which correspond to resources that can be duplicated. See any introduction to linear logic for more details.

Affine logic is a version of linear logic where propositions can be "thrown away", that is, where the rule `p * q |- p` holds for all `p` and `q`. The reason we use affine logic here is that it is useful for describing a notion of _permissions_, where each `p` intuitively corresponds to permission to perform a particular action. It is always justified to forget some permission if you are not going to use it, but you can't in general give yourself more permissions. One of the central permissions used in Heapster is the permission to access memory through a particular pointer. The simplest form of this is the pointer permission `x:ptr((rw,off) |-> p)`, that represents a permission to read &mdash; and possibly write, depending on `rw` &mdash; memory at offset `off` from `x`, along with permission `y:p` to whatever value `y` is currently stored there. The `array` and `memblock` permissions also represent different forms of permission to read and possibly write memory, with different stipulations on the permissions held for the values currently stored there. Read-only permissions are copyable, meaning that `x:ptr((R,off) |-> p) |- x:ptr((R,off) |-> p) * x:ptr((R,off) |-> p)` can be proved in Heapster, as long as `p` does not contain any write permissions, while write permissions `x:ptr((W,off) |-> p)` are not. This corresponds to the one-writer or multiple readers paradigm of, e.g., Rust.

The remainder of this section explains Heapster implication.


## Permission Implication Rules

At any given point during type-checking and/or implication proving, Heapster maintains a _permission set_ that describes the current permissions to various objects that are currently held by the program. Permission sets are defined by the `PermSet` type in Permissions.hs, and have two components: the _permissions map_, which maps each variable `x` in scope to what is called the _primary_ permission held on `x`; and the _permissions stack_, which represents the permissions that are actively being used or manipulated. We write a permission set as:

```
x1 -> px1 * ... * xm -> pxm; y1:p1 * ... * yn:pn
```

The portion before the semicolon represents the permissions map, which maps each `xi` to its primary permission `pxi`, while the portion after the semicolon represents the permissions stack, containing permissions `y1:p1` through `yn:pn` in sequence. The final permissions `yn:pn` is the top of the stack. We often write `PS` for a permission set.

The general form of permission implication is the judgment

```
PS |- (z1_1, ..., z1_k1 . PS1) \/ ... \/ (zn_1, ..., zn_kn . PSn)
```

which says that, starting with permission set `PS` on the left-hand side of the turnstyle `|-`, we can prove one of the permission sets `PSi` on the right-hand side. Each disjunctive case could introduce 0 or more existential variables `zi_1, ..., zi_ki`, which can be used in the corresponding permission set `PSi`. We often omit the permissions map and/or the existential variables when they are not necessary; e.g., we write `PS1 |- PS2` instead of `PS1 |- ( [] . PS2)`. We also tend to omit the permissions map from implications, as permissions maps almost never change; thus, e.g., we might write `x:p |- y:q` instead of `x1 -> px1 * ... * xm -> pxm; x:p |- x1 -> px1 * ... * xm -> pxm; y:q`.

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


[comment]: <> (FIXME: Implementation of the rules: `simplImplIn` and `simplImplOut`, `applyImpl1`: these all check for correct perms)

[comment]: <> (FIXME: Explain overall pattern of the simplimpl rules: intro vs elim rules for most constructs)

