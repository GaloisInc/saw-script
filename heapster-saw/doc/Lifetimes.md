
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
the permission `x:[l]ptr((R,0) |-> Q)`, where `Q` is recursively a permission
that ensures `P` is still valid. More generally, if we define the permission
transformer

```
READ(l)(ptr((rw,off) |-> P)) = [l]ptr((R,off) |-> READ(l)(P))
READ(l)(P) = P (if P is not a pointer permission)
```

that recursively turns all pointer permissions into read permissions in lifetime
`l`, then `READ(l)(P)` is a much weaker permission (in terms of being easier to
satisfy) than `P` but that still ensures `P` is valid.

More formally, Heapster combines all of the permissions returned when a lifetime
is ended, along with all the permissions required to prove that those returned
permissions are still valid, into the lifetime ownership permission introduced
above. The general form of the lifetime ownership permission in Heapster is as
follows:

```
l:lowned[ls](Ps_in -o Ps_out)
```

The `ls` argument is a list of the sub-lifetimes of `l`, meaning those lifetimes
whose temporal duration is contained inside `l`. These are discussed below. The
permission set `Ps_out` lists all the permissions that are returned after `l` is
finished. The permission set `Ps_in` lists all the permissions needed to prove
that the permissions `Ps_out` are still valid. The rule to end a lifetime is

```
Ps_in * l:lowned(Ps_in -o Ps_out)
|-
Ps_out * l:lfinished
```

This states that the current process must hold permissions `Ps_in` to prove that
the permissions held in the lifetime `l` are still valid. After the lifetime is
finished it gets back `Ps_out` along with a permission `l:lfinished` stating
that `l` is in the finished state. Note that this looks very much like an
implication elimination rule, where permission `l:lowned(Ps_in -o Ps_out)` is
"applied" to "input" permissions `Ps_in` to yield "output" permissions `Ps_out`.
The functional specification extracted from an `lowned` permission is in fact a
function; this is discussed below.


Our temporal splitting rule now looks like this:

```
x:P * l:lowned(Ps_in -o Ps_out)
|-
x:LIFETIME(l)(P) * l:lowned(x:READ(l)(x:READ(l)(P),Ps_in -o x:P,Ps_out)
```

where `LIFETIME(l)(P)` recursively sets the lifetime of all pointer permissions
in `P` to `l`, in a manner similar to the definition of `READ(l)`. This rule
allows a permission `P` to be temporally split into the portion `LIFETIME(l)(P)`
that is valid while `l` is active and a copy of `P` inside the lifetime
ownership permission for `l` that can only be used after `l` is finished. It
also states that a process can now only end `l` if it can prove that `P` is
still valid by proving the read-only version of `P` relative to `l`.


## Lifetimes Containing Lifetimes

- If we already have a permission in a lifetime, we might want to temporally split that
    permission again; this results in nested lifetimes

- Nested lifetimes are captured in the `lowned` permissions

- The permission `l:[l2]lcurrent` states that `l` is current whenever `l2` is,
  meaning that `l2` is contained as a nestred lifetime inside `l`

- Prove `lcurrent` permimssions by reflexivity, transitivity, and `lowned` permissions

- Cannot end a lifetime until all of its nested lifetimes are finished;
  implication rule removes a nested lifetime from an `lowned` permission when
  the nested lifetime is `lfinished`


## Lifetime Implication Rules


## Example: Typing an Accessor Function

