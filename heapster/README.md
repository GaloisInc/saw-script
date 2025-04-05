# Heapster

Implementation of the Heapster type system of separation types inside SAW,
including a translation to SAWCore.

The remainder of this README contains general information about using
Heapster about the `examples` directory contained here.

## Building

You will need to follow the instructions in the top-level README to download
or build a SAW binary, of which Heapster is a part.

If you intend to interact with any of Heapster's Coq output, you will also need
to follow the instructions in the README in the `saw-core-coq` subdirectory.
Specifically, after installing the dependencies, you will need to run the
following (from this directory):
```bash
cd ../saw-core-coq/coq
make
```

## Using Heapster

This section will walk through the process of using Heapster on some code in a
C file. This will involve generating LLVM bitcode from your file, writing a SAW
script to type-check your code with Heapster, and writing a Coq file to prove
things about the generated functional specification(s).

### Generating LLVM bitcode

The input to Heapster is an LLVM bitcode (`.bc`) file. To generate LLVM
bitcode from a C file, run the following:
```bash
clang -emit-llvm -g -c my_file.c
```
Be aware that the resulting bitcode may depend on your `clang` version and your
operating system. In turn, this means the Heapster commands in your SAW script
and the proofs in your Coq file may also be dependent on how and where the
bitcode is generated. For this reason, we provide bitcode files for every
example in the `examples` directory.

### Type-checking using a SAW script

To use Heapster on your generated bitcode, you can either write a SAW script
(e.g. `my_file.saw`) or start a SAW interactive session. This document will
use writing a SAW script as an example, but the commands are the same in
either case.

To see the documentation for any of the commands mentioned here, type `:help`
followed by the name of the command in a SAW interactive session.

In order to use Heapster commands, you must begin with:
```
enable_experimental;
```
You can then load your example bitcode file into Heapster using the following:
```
env <- heapster_init_env "my_file" "my_file.bc";
```
This file will not go into detail about the process of actually type-checking a
function with Heapster. Instead, we will briefly discuss a few of the main
commands used, as well as some examples.

One of the simplest Heapster commands is `heapster_define_perm`, which defines
a new named permission which can then be used in Heapster types. As an
example, the following defines a permission which describes a 64-bit integer
value:
```
heapster_define_perm
  env
  "int64"
  " "
  "llvmptr 64"
  "exists x:bv 64.eq(llvmword(x))";
```
The first argument is the Heapster environment, the second is its name, the
third is its arguments (of which there are none), the fourth is the type of
value that the permission applies to, and the fifth is its definition. 

To define [permissions](doc/Permissions.md) which can describe unbounded data structures, you can use
the `heapster_define_recursive_perm` command. As an example, here is how to
describe a linked list of 64-bit words using this command:
```
heapster_define_recursive_perm
  env
  "List64"
  "rw:rwmodality"
  "llvmptr 64"
  ["eq(llvmword(0))", "ptr((rw,0) |-> int64<>) * ptr((rw,8) |-> List64<rw>)"]
  "List (Vec 64 Bool)"
  "foldList (Vec 64 Bool)"
  "unfoldList (Vec 64 Bool)";
```
Its first four arguments are the same as for `heapster_define_perm`, its
fifth argument contains its different inductive cases (in this case, a `List64`
is either a null pointer, or a pointer to an `Int64` and another `List64`),
and its final three arguments are its translation into SAW core. Here the
SAW core definitions used are from the SAW core prelude, but if you need new
SAW core definitions, you will need to use the following command instead of 
`heapster_init_env`:
```
env <- heapster_init_env_from_file "my_file.sawcore" "my_file.bc";
```

Finally, to actually type-check a function you can use
`heapster_typecheck_fun`. The following is an example using the `is_elem`
function from `examples/linked_list.c` and the permissions we defined above:
```
heapster_typecheck_fun
  env
  "is_elem"
  "().arg0:int64<>, arg1:List64<R> -o arg0:true, arg1:true, ret:int64<>";
```
The heapster type given has three parts, the context of ghost variables, the
input permissions, and the output permissions. Here there are no ghost
variables used, so the context is empty (the `()` at the start). The input
permissions state that the two arguments to `is_elem` are an `int64` and a
read-only `List64`, respectively. The output permissions state that the two
arguments are unconstrained after returning (the vacuous `true` permissions)
and that the returned value is an `int64`.

Note that for more complicated examples, usually examples involving loops,
the `heapster_block_entry_hint` command will also need to be used in order for
the `heapster_typecheck_fun` command to succeed. In the case of functions with
loops, this hint corresponds to a loop invariant. Additionally, such examples
will also often require your unbounded data structure to be defined as a
reachability permission, using `heapster_define_reachability_perm`, instead of
just as a recursive permission. See `examples/iter_linked_list.saw` for some
examples of using the commands mentioned in this paragraph.

Once you're finished, use the following command to export all the type-checked
functions in the current environment as functional specifications in Coq. By
convention, we add a `_gen` suffix to the filename.
```
heapster_export_coq env "my_file_gen.v";
```

### Heapster Permissions

See this [additional documentation](doc/Permissions.md) for a reference on the syntax and meaning of heapster permissions.

### Verifying in Coq

To interact with the generated Coq code, you will first need to set up your Coq
environment. Make a file named `_CoqProject` with the following contents,
where `PATH_TO_SAW` is replaced by the path to the top-level `saw-script`
directory:
```
-Q PATH_TO_SAW/saw-core-coq/coq/generated/CryptolToCoq   CryptolToCoq
-Q PATH_TO_SAW/saw-core-coq/coq/handwritten/CryptolToCoq   CryptolToCoq

my_file_gen.v
```
This file is already set up for the examples in the `examples` directory.

By convention, the file which contains proofs about functions in your file
has the `_proofs` suffix added (e.g. `my_file_proofs.v`). This file should
also be added to your `_CoqProject`.

In your `_proofs` file, you will want to import at least the following:
```coq
From CryptolToCoq Require Import SAWCorePrelude.
From CryptolToCoq Require Import CompMExtra.
```

You can then either load your file using `Load` (e.g. `Load "my_file_gen.v"`)
or make `-Q . Namespace`, where `Namespace` is whatever string you want, the
third line of your `_CoqProject` and use `Import` (e.g.
`Require Import Namespace.my_file_gen`). You will then need to import the
module from your generated file as well as the SAW core prelude module – all
together these lines should look like:
```coq
Load "my_file_gen.v".
Import my_file.
Import SAWCorePrelude.
```

Often the first thing you want to verify is that the generated specification
has no errors. Errors can appear because of errors in the LLVM bitcode or
because of errors in the type-checking process. Having errors of the first kind
in the generated specification is not an issue, but it must be proved that they
are never reached. Sometimes, a precondition and/or loop invariant must be
added in order for such a proof to be completed, see
`examples/arrays_proofs.v` for an example. In a generated spec, these errors
often look like the following:
```
errorM "Failed Assert at arrays.c:19:14"
```
Seeing an error of the second kind in your generated specification means you
need to revise the types you wrote in your SAW script. These errors are
usually quite distinctive in the generated Coq code, for example:
```
errorM "At is_elem.c:26:12 ($10 = call $9($3, $7);)
  Regs: $9 = fn @ , $3 = ptr @ , $7 = ptr4 @ 
  Input perms: top_ptr:eq(LLVMword ghost_bv),
               top_ptr1:ptr((R,0) |-> int64<>)*ptr((R,8) |-> List64<R>),
               ghost_frm:llvmframe [C[&l]:8, C[&x]:8, local_ptr:8],
               fn:().
                  arg1:int64<>, arg:List64_nonnull<R>
                  -o
                  arg1:true, arg:true, ret:int64<>, ptr:eq(LLVMword ghost_bv),
               ptr4:eq(ptr3), local_ptr:ptr((W,0) |-> true),
               C[&x]:ptr((W,0) |-> eq(ptr)), C[&l]:ptr((W,0) |-> eq(ptr1)),
               ghost_bv:true, ptr3:List64<R>, ptr1:eq(top_ptr1)
  Could not prove (). ptr:int64<>, ptr4:List64_nonnull<R>

  proveVarImplH: Could not prove
  ptr3:eq(LLVMword 0)
  -o
  (). ptr((R,0) |-> int64<>)*ptr((R,8) |-> List64<R>)"
```

To prove no-errors you will prove that your generated specification **refines**
the specification `noErrorsSpec`, which is defined as follows:
```coq
Definition noErrorsSpec : CompM A := existsM (fun x => returnM x).
```

For example, the statement of no-errors for `is_elem` is the following:
```coq
Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
```

You can think of specifications in the `CompM` monad (such as `noErrorsSpec`
and everything Heapster generates) as sets of possible executions, and the
refinement relation as the subset relation on these sets. In this way,
`noErrorsSpec` represents the set of all computations which return some pure
value (and thus cannot contain any calls to `errorM : string -> CompM A`), and
thus, proving that a specification refines `noErrorsSpec` represents proving
that it always returns some pure value.

For the proof of `no_errors_is_elem`, we simply need to unfold both sides of
the refinement, then call the automated tactic `prove_refinement`, imported
from `CompMExtra`:
```coq
Proof.
  unfold is_elem, is_elem__tuple_fun, noErrorsSpec.
  prove_refinement.
Qed.
```

The `prove_refinement` tactic is not guaranteed to solve all goals. Sometimes,
the goals it leaves over can be completed with simple Coq tactics, and other
times the left over goals can help you discover that the lemma you're trying
to prove is false, and therefore you need to return to type-checking, or
add/revise your precondition and/or loop invariant. In this case, the tactic
was able to solve all goals.

Note that when the generated specification has functions bound by a `letRecM`,
there must be a `letRecM` with matching shape on the right of a refinement.
To help set this up, you can use the `prove_refinement_match_letRecM_l` tactic,
which will generate as many goals as there are functions needed for the
`letRecM` on the right hand side. As an example, here is an excerpt from
`examples/iter_linked_list_proofs.v`, where a single matching `letRecM`
function is needed:
```coq
Lemma no_errors_is_elem : refinesFun is_elem (fun _ _ => noErrorsSpec).
Proof.
  unfold is_elem, is_elem__tuple_fun.
  prove_refinement_match_letRecM_l.
  - exact (fun _ _ => noErrorsSpec).
  unfold noErrorsSpec.
  prove_refinement.
Qed.
```
It is good practice to defer unfolding the right hand side until after
the `letRecM` functions have been added to avoid `prove_refinement` getting
ahead of itself.

Check out the examples directory for more examples of what sort of things you
can prove about generated specifications.

## Examples

The `examples` directory contains lots of varied examples of the entire process
described above. To run all of the SAW scripts and Coq proofs, you can simply 
run `make`, assuming that all `*_gen.v` files that may have been left from a
previous run have been deleted (alternately, you can first run `touch *.saw`).

Here is a brief overview of the different examples.
- `linked_list` - This is a good set of examples to look at first.
  `linked_list.saw` introduces the basics of Heapster type-checking, and
  `linked_list_proofs.v` contains lots of varied proofs all of which are
  relatively very easy to understand.
- `iter_linked_list` - This is a good set of examples to look at after the
  above, as they are variants of the above, just written with loops instead of
  recursion. These examples introduce reachability permissions, block entry
  hints, and preconditions in Coq proofs.
- `loops` - Some more examples of functions with loops, but which do not
  involve reachability permissions or preconditions. This set of examples
  introduces functions which depend on other functions, see `loops_proofs.v`.
- `arrays` - This set of examples involves using multiple types of hints during
  type-checking as well as preconditions, loop invariants, and lots of user
  input post-`prove_refinement` on the Coq side. 
- `mbox` - This is a set of examples based on "real-world" code, i.e. code
  not written for the intent of testing Heapster. As such, not every function
  is complete, and the most complicated examples can be found in this file.
- `iso_recursive` - This set of examples uses an experimental feature where
  the SAW core definitions used when defining recursive permissions are
  set automatically.

Additionally, `clearbufs`, `xor_swap`, `memcpy`, and `string_set` contain some
minimal examples of type-checking various simple functions.

Not included in this list are any of the rust examples.
