
# Lifetimes in Heapster

In this document, we describe the design of the portions of the Heapster type
system concerning lifetimes. The motivation for lifetimes in Heapster is to
capture the pattern of a unique write permission being temporarily demoted to a
shared read permission.

Difficulties:
* Non-lexical, meaning it does not rely on regular code structure, since this
  needs to work at the LLVM level, which does not have this structure; stated
  differently, the type-checker doesn't know a priori when the write becomes a
  shared read or when the code is done with that and it is time to switch back
* Since shared read permissions are copyable, there is no way to ensure that you
  have gotten back all the shared read permissions when you want to go back to
  unique write, so you need some way to invalidate all those shared read
  permissions


The Heapster solution to this problem is the notion of a _lifetime_. A lifetime
in Heapster is an object `l` that represents a period of time. At any point
during execution, a lifetime can either be _active_, meaning that period of time
has not yet completed, or it can be _finished_, meaning that it has completed.
The idea is that we can model a unique write permission being temporarily
demoted to a shared read permission by associating that demotion with a lifetime
`l`. While `l` is active, the shared read permissions can be used, but the
unique write permission is "saved for later" in the lifetime `l`. Once `l` is
finished, marking that the temporary demotion is over, the shared read
permissions are no longer valid and the original unique write permission can be
recovered and used again.


## Lifetime Modalities and Ownership

To model temporary permissions that are only valid while a lifetime is active,
many Heapster permissions contain a lifetime modality that marks them as
temporary permissions in a lifetime. For instance, the permission

```
x:[l]ptr ((R,0) |-> P)
```

is a permission that allows reading offset `0` of pointer value `x`, but only
while lifetime `l` is active. This is how one would write a temporary read
permission.

In order to use such a permission, the current process must prove to the type
system that `l` is indeed active. In order to do this, the process must _own_
the lifetime `l`, meaning it must own the sole, unique permission that permits
the holder to control when `l` finishes. Otherwise, some other concurrent
process could presumably end `l` out from under the current process and make the
permission invalid. Lifetime ownership can be represented with the _simple
lifetime ownership permission_:

```
l:lowned (x1:P1,...,xn:Pn)
```

(Note that there is a more general lifetime ownership permission discussed
below.) This permission states that `l` is currently active, and that the
current process has the sole, unique permission to end `l`. When the current
process ends `l` , it will recover permissions `x1:P1,...,xn:Pn`. These are the
permissions that were "saved for later" in the lifetime `l`. Using this
permission construct along with the lifetime modalities discussed above, a
unique write permission that has temporarily been demoted to a shared read can
be modeled with the permissions

```
l:lowned (x:ptr((W,0) |-> P)), x:[l]ptr((R,0) |-> P)
```

Heapster also allows write permissions with lifetime modalities, such as the
permission `x:[l]ptr ((W,0) |-> eq(0))`. This states that the current process
can write to the value pointed to by `x`, and that that value is currently equal
to `0`. Temporary write permissions lead to one of the key complexities with
lifetimes in Heapster. Say a process has the permissions

```
l:lowned (x:ptr((W,0) |-> eq(0))), x:[l]ptr((W,0) |-> eq(0))
```

These state that the process can write to pointer `x`, and can also end lifetime
`l`, at which point it will get back permission `x:ptr((W,0) |-> eq(0))`.
However, because it has write permission to `x`, it could potentially write a
`1` to pointer `x` before ending lifetime `l`. In this case, `x` would point to
`1`, but the process would get back permission `x:ptr((W,0) |-> eq(0))`, stating
that `x` points to `0`, a contradiction!

To solve this problem, Heapster requires a process to prove that the permissions
held by a lifetime are still valid before it ends that lifetime. To do this, the
process must hold read versions of the permissions it is getting back by ending
the lifetime, relativized to the lifetime being ended. For example, in order to
end lifetime `l` with permissions

```
l:lowned (x:ptr((W,0) |-> eq(0)))
```

the current process must hold permission

```
x:[l]ptr((R,0) |-> eq(0))
```

This is enough to prove that `x` still points to a `0` value.


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

