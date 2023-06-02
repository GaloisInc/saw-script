
# Lifetimes in Heapster

In this document, we describe the design of the portions of the Heapster type
system concerning lifetimes. Lifetimes are Heapster's way of capturing notions
of time and "temporariness" of permissions. The primary motivation for lifetimes
in Heapster is to capture the pattern of a unique write permission being
temporarily demoted to a shared read permission. Heapster lifetimes are also
useful for modeling Rust lifetimes, which can be used to define temporary write
permissions as well as temporary read permissions. See [here](Permissions.md)
for a reference on Heapster's permission language and [here](Rules.md) for a
high-level overview of Heapster's notion of permission implication.

There are two difficulties that arise in trying to represent a unique write
permission being temporarily demoted to a shared read permission in Heapster.
First, the approach must be non-lexical, meaning it does not rely on regular
code structure. This is the case because Heapster is a type system for LLVM,
which does not have this sort of structure. Stated differently, the Heapster
type-checker doesn't know a priori when the write becomes a shared read or when
the code is done with that and it is time to switch back.

The second difficulty in representing this pattern in Heapster is ensuring that
no process can use a shared read permission after it is time to recover the
original unique write permission. Since shared read permissions are copyable,
any number of copies of the temporary shared read permissions can be made, and
there is no way to ensure that you have gotten back all the shared read
permissions when you want to go back to unique write. One approach to this
problem is fractional permissions (FIXME: citation), but that requires tracking
an abstract notion of permission fractions through the implications, which can
actually be onerous in type-checking a large program. Instead, what is needed is
a way to invalidate all the temporary shared read permissions when it is time to
recover the unique write.



## Temporally Splitting Permissions

The Heapster approach to modeling temporary permissions uses the notion of a
_lifetime_. A lifetime in Heapster is an object `l` that represents a period of
time. At any point during execution, a lifetime can either be _active_, meaning
that period of time has not yet completed, or it can be _finished_, meaning that
it has completed. The idea is that we can temporally split a permission into a
temporary permission that is only valid while a lifetime `l` is active, along
with a permission that is "saved for later" and is only valid after `l` is
finished. For instance, to model a unique write permission being temporarily
demoted to a shared read permission, we first split the unique write permission
into a write permission during `l` and a write permission after `l`. We can then
demote the former permission from write to read, and use it as a temporary read
permission that can only be used while `l` is active. Once `l` is finished,
marking that the temporary demotion is over, the shared read permissions are no
longer valid and the original unique write permission can be recovered and used
again.

Aspirationally, the easiest way to achieve this idea would be to have a temporal
splitting rule that looks something like this:

```
x:ptr((W,0) |-> P)
|-
x:[l]ptr((W,0) |-> P) * x:[AFTER(l)]ptr((W,0) |-> P)
```

The left-hand side is a permission to write to the value pointed to by `x`, with
the assumption that we hold permission `P` to the value currently there. The
right-hand side has two versions of this permission, one with modality `[l]`,
meaning that the permission is only valid while `l` is active, and one with
modality `[AFTER(l)]`, meaning that the permission is only valid after `l` is
finished. This rule makes intuitive sense: the permission to do something at any
point is the same as the combination of the permission to do it now with the
permission to do it later. It also has nice compositionality properties, that
work well with the frame rule. For instance, to model a unique write permission
temporarily being turned into two shared read permissions (say, for two copies
of `x` being passed in a function call), we could perform these implication
steps:

```
x:ptr((W,0) |-> P)
|-
x:[l]ptr((W,0) |-> P) * x:[AFTER(l)]ptr((W,0) |-> P)
|-
x:[l]ptr((R,0) |-> P) * x:[AFTER(l)]ptr((W,0) |-> P)
|-
x:[l]ptr((R,0) |-> P) * x:[l]ptr((R,0) |-> P) * x:[AFTER(l)]ptr((W,0) |-> P)
```

The first step is the temporal splitting rule, the second demotes write to read,
and the third duplicates the shared read permission. These last two steps
operate compositionally on just the left-hand permission, with no need to
refer to the `[AFTER(l)]` permission at all.

In order to use such a temporary `[l]` permission, the current process must
prove to the type system that `l` is indeed active. In order to do this, the
process must _own_ the lifetime `l`, meaning it must own the sole, unique
permission that permits the holder to control when `l` finishes. Otherwise, some
other concurrent process could presumably end `l` out from under the current
process and make the permission invalid. Lifetime ownership can be represented
with the _lifetime ownership permission_:

```
l:lowned ()
```

This permission states that `l` is currently active, and that the current
process has the sole, unique permission to end `l`. We discuss this permission
more below.


Unfortunately, this scheme as described suffers from a flaw: there is nothing
about the `[AFTER(l)]` modality that ensures its permission is still valid when
`l` finishes. The problem comes from temporary write permissions such as
`x:[l]ptr((W,0) |-> P)`. This permission allows the process holding it to write
_any_ value to the pointer `x`, not just one on which we hold permissions `P`.
This is necessary for a type system like Heapster that operates on low-level
machine code, which will often require multiple instructions to re-establish a
typing invariant like `P` on a pointed-to value. This in turn means that a
process could change the value pointed to by `x` to one that it does not hold
permissions `P` on, and then end the lifetime `l`, giving back permissions
`x:ptr((W,0) |-> P)`, even though the process does not hold permissions `P` to
the value pointed to by `x`. This yields a contradiction.


## Proving Validity When Ending Lifetimes

To solve this problem, Heapster requires that whenever a process ends a lifetime
it must prove that the permissions that are given back by the lifetime are still
valid. In order to prove a pointer permission `x:ptr((W,0) |-> P)` is still
valid, the current process needs to prove that, just before `l` ends, `x` points
to a value on which permission `P` is still valid. This is precisely captured by
the permission `x:[l]ptr((R,0) |-> Q)`, the temporary read-only version of the
original permission, where `Q` is recursively a permission that ensures `P` is
still valid.

More formally, Heapster combines all of the permissions returned when a lifetime
is ended, along with all the permissions required to prove that those returned
permissions are still valid, into the lifetime ownership permission introduced
above. The general form of the lifetime ownership permission in Heapster is as
follows:

```
l:lowned[l1,...,ln](Ps_in -o Ps_out)
```

The lifteimes `l1,...,ln` are a list of the sub-lifetimes of `l`, meaning those
lifetimes whose temporal duration is contained inside `l`. These are discussed
below. When this list is empty, the brackets are omitted. The permission set
`Ps_out` lists all the permissions that are returned after `l` is finished. The
permission set `Ps_in` lists all the permissions needed to prove that the
permissions `Ps_out` are still valid. The rule to end a lifetime is

```
Ps_in * l:lowned(Ps_in -o Ps_out)
|-
Ps_out * l:lfinished
```

This states that the current process must hold permissions `Ps_in` to prove that
the permissions held in the lifetime `l` are still valid. After the lifetime is
finished it gets back `Ps_out` along with a permission `l:lfinished` stating
that `l` is in the finished state.

In order to define the permission needed to prove that a temporally split
permission is still valid when a lifetime end, Heapster defines a _lifetime
functor_ as a function from a lifetime `l` and 0 or more read-write modalities
`rw1,...,rwn` using the following syntax:

```
F (l,rw1,...,r2n) ::=
P (without l or any rwi free)
|
[l]ptr((rwi,off) |-> F(l,rw1,...,r2n))
(where off contains none of l or the rwi)
|
... (similar cases for memblock and array permissions)
```

Intuitively, a lifetime functor `F` is a way of specififying some possibly
nested pointer permissions whose lifetimes are all given by the same `l` and
whose read-write modalities are given by the arguments `rw1,...,rwn`. Heapster
also defines the lifetime `always` that is guaranteed to always be current, in
order to express pointer permissions not in a lifetime. In order to prove a
permission `F(always,rw1,...,rwn)` is still valid when lifetime `l` for an
arbitrary lifetime functor `F`, it is sufficient to prove the read-only version
`F(l,R,...,R)` that is relative to lifetime `l`.

Our temporal splitting rule now looks like this, where we use `rws` as a
meta-variable for a list of read-write modalities:

```
x:F(always,rws) * l:lowned(Ps_in -o Ps_out)
|-
x:F(always,rws) * l:lowned(x:F(l,R,...,R),Ps_in -o x:F(always,rws),Ps_out)
```

This rule allows a permission `P=F(always,rws)` to be temporally split into the
portion `F(l,rws)` that is valid while `l` is active and a copy of `P` inside
the lifetime ownership permission for `l` that can only be used after `l` is
finished. It also states that a process can now only end `l` if it can prove
that `P` is still valid by proving the read-only version `F(l,R,...,R)` of `P`
relative to `l`.

The rule for ending a lifetime looks very much like an implication elimination
rule, where permission `l:lowned(Ps_in -o Ps_out)` is "applied" to "input"
permissions `Ps_in` to yield "output" permissions `Ps_out`. In fact, in the
specification extraction process that Heapster performs to generate a functional
specification of an imperative program, the lifetime ownership permission
`l:lowned(Ps_in -o Ps_out)` is translated to the type of monadic functions from
the translation of `Ps_in` to the translation of `Ps_out`.

FIXME: explain the functional translation and how it is like a lens


## Lifetimes Containing Lifetimes

As a natural extension of this system, what if the permission we are trying to
split temporally is already inside a lifetime? That is, what if we have a
temporary permission relative to lifetime `l1` and we need to temporally split
it into portions before and after some lifetime `l2`? This pattern is very
common in modeling Rust code, as is discussed in the [Rust translation
document](RustTrans.md). Intuitively, this only makes sense if `l2` is a
_sub-lifetime_ of `l1`, meaning that `l2` is guaranteed to end before `l1`.
Otherwise, there is no portion of the temporary `l1` permission after `l2` has
ended. (At a technical level, temporally splitting a permission already in a
lifetime with respect to anther lifetime is possible without sub-lifetimes, but
the logic gets more complicated in a way that is not useful in practice.)

To represent the notion of sub-lifetimes, the lifetime ownership permission

```
l:lowned[l1,...,ln](Ps_in -o Ps_out)
```

includes a list `l1,...,ln` of the sub-lifetimes of `l`. The logical requirement
for sub-lifetimes is that no lifetime can end until all of its sub-lifetimes
have ended. To capture this requirement in the logic, the rule for ending
lifetimes requires that the sub-lifetime list is empty for the lifetime being
ended. (Note that the rule for ending lifetimes displayed above already has this
requirement.) Any lifetime can be _subsumed_ inside another, marking it as a
sub-lifetime, using this rule:

```
l1:lowned[ls] (ps_in -o ps_out)
|-
l1:lowned[l2,ls] (ps_in -o ps_out)
```

To remove a sub-lifetime from an `lowned` permission, the sub-lifetime must be
finished. This is captured with the following rule:

```
l1:lowned[ls1,l2,ls2] (ps_in -o ps_out) * l2:lfinished
|-
l1:lowned[ls1,ls2] (ps_in -o ps_out)
```

To represent the fact that a lifetime `l2` is a sub-lifetime of `l1`, Heapster
includes the permission `l1:[l2]lcurrent`. Technically, this states that `l1` is
current whenever `l2` is. Heapster includes rules for reflexivity of this permission:

```
|- l:[l]lcurrent
```

along with transitivity:

```
l1:[l2]lcurrent * l2:[l3]lcurrent |- l1:[l3]lcurrent
```

It also includes the following rule for proving this permission from a
sub-lifetime list in an `lowned` permission:

```
l1:lowned[ls1,l2,ls2] (ps_in -o ps_out)
|-
l1:[l2]lcurrent * l1:lowned[ls1,l2,ls2] (ps_in -o ps_out)
```

Note that the `lowned` permission remains the same between the left- and
right-hand sides, with the only difference being the addition of the `lcurrent`
permission on the right.

- Mention that `always:[l]lcurrent` is always true, but isn't actually
  represented as a permission in Heapster because Heapster requires the lhs to
  be a variable

- Use `lcurrent` in the load and store rules

- Use `lcurrent` permissions in the new temporal splitting rule, as well as the
  lifetime weakening rule


## Example: Typing an Accessor Function

