
# Lifetimes in Heapster

In this document, we describe the design of the portions of the Heapster type
system concerning lifetimes. Lifetimes are Heapster's way of capturing notions
of time and "temporariness" of permissions. The primary motivation for lifetimes
in Heapster is to capture the pattern of a unique write permission being
temporarily demoted to a shared read permission. Heapster lifetimes are also
useful for modeling Rust lifetimes, which can be used to define temporary write
permissions as well as temporary read permissions.


Difficulties:
* Non-lexical, meaning it does not rely on regular code structure, since this
  needs to work at the LLVM level, which does not have this structure; stated
  differently, the type-checker doesn't know a priori when the write becomes a
  shared read or when the code is done with that and it is time to switch back
* Since shared read permissions are copyable, there is no way to ensure that you
  have gotten back all the shared read permissions when you want to go back to
  unique write, so you need some way to invalidate all those shared read
  permissions



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
with the _simple lifetime ownership permission_:

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


## Ensuring Validity When Ending Lifetimes

To solve this problem, Heapster requires that whenever a process ends a lifetime
it must prove that the permissions that are given back by the lifetime are still
valid. In order to formalize this in the Heapster type system, Heapster puts all
of the "after" permissions inside the lifetime ownership permission. The
simple version of the lifetime ownership permission looks like this:

```
l:lowned (x1:P1,...,xn:Pn)
```

The additional structure indicates that, when the current process ends `l` , it
will recover permissions `x1:P1,...,xn:Pn`. These are the permissions that were
"saved for later" in the lifetime `l`. Our temporal splitting rule now looks
like this:

```
x:ptr((W,0) |-> P) * l:lowned(x1:P1,...)
|-
x:[l]ptr((W,0) |-> P) * l:lowned(x:ptr((W,0) |-> P),x1:P1,...) * 
```

Rather than adding an `AFTER(l)` to express the permission that is returned
after `l` is finished, this rule adds that permission to the `lowned` permission
for `l`. This "bundles" all of the permissions that are returned when `l` is
finished into one place, rather than having them be separate permissions.

To end lifetime `l`, Heapster then requires that the current process prove that
all the permissions in the `lowned` permission are still valid. To do this, it
is sufficient to hold a temporary read version of each permission relative to
the lifetime being ended. This is intuitively the least permission that ensures
that the required pointer structure is still valid. More formally, we
recursively define the permission transformer

```
[l](R) (ptr((rw,off) |-> P)) = [l]ptr((R,off) |-> [l](R)P)
[l](R) (P) = P (if P is not a pointer permission)
```

that changes all pointer permission to be temporary read permissions relative to
lifetime `l`. The rule for ending a lifetime is then:

```
[l](R)Ps * l:lowned(Ps)
|-
Ps
```



(FIXME: the remainder is an outline)

More general lifetime ownership permission has the form

```
l:lowned[ls] (x1:P1,... -o y1:Q1,...)
```

* The `ls` are the lifetimes subsumed by `l`, meaning that they are guaranteed
to end before `l` does

* The left-hand side `x1:P1,...` are the permissions that must be "given back"
  in order to prove that the right-hand side permisisons are still valid;
  Intuitively, these correspond to the outstanding borrows that are "checked
  out" from the lifetime `l` and must be "returned" before `l` ends

* The right-hand side `y1:Q1,...` are the permissions that are given back to the
  process when it ends `l`

