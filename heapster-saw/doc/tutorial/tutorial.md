# Tutorial to learn the basics of heapster-saw

This tutorial extends the current README with enough details and
examples to get anyone up to speed with using and hacking on Heapster.

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [Tutorial to learn the basics of heapster-saw](#tutorial-to-learn-the-basics-of-heapster-saw)
    - [Building](#building)
        - [Build Saw](#build-saw)
        - [Build the Coq backend for Saw](#build-the-coq-backend-for-saw)
        - [Build all the examples](#build-all-the-examples)
    - [A quick tour of SAW](#a-quick-tour-of-saw)
        - [Overview](#overview)
        - [Running an example](#running-an-example)
            - [1. Compile the code.](#1-compile-the-code)
            - [2. Run the saw interpreter](#2-run-the-saw-interpreter)
            - [3. Load the file and extract the two function specifications.](#3-load-the-file-and-extract-the-two-function-specifications)
            - [4. Define the equality theorem.](#4-define-the-equality-theorem)
            - [5. Call the SAT/SMT solver to prove the theorem.](#5-call-the-satsmt-solver-to-prove-the-theorem)
        - [Batch scripts](#batch-scripts)
    - [Using Heapster](#using-heapster)
        - [Heapster type-checking overview](#heapster-type-checking-overview)
        - [First example](#first-example)
        - [Pointers](#pointers)
        - [Structs](#structs)
        - [Batch scripts](#batch-scripts-1)
        - [Arrays](#arrays)
        - [Recursive data structures](#recursive-data-structures)
            - [1. Generating LLVM bitcode](#1-generating-llvm-bitcode-1)
            - [2. Run the SAW interpreter with Heapster](#2-run-the-saw-interpreter-with-heapster-1)
            - [3. Load the file and extract the function types.](#3-load-the-file-and-extract-the-function-types)
            - [4. Writing heapster types for your functions](#4-writing-heapster-types-for-your-functions-1)
                - [Defining list permissions](#defining-list-permissions)
            - [5. Type-check your program](#5-type-check-your-program-1)

<!-- markdown-toc end -->


## Building

We'll start by building everything you need to use Heapster. All the
commands here are with respect to the top-level `saw-script` directory.

### Build Saw 
 
You will need to follow the instructions in the top-level [README](../../README.md) to
download or build a SAW binary, of which Heapster is a part. In
particular, make sure you follow the instructions to install Z3. Once `./build.sh`
succeeds it should report 

```bash
COPIED EXECUTABLES TO /Path/To/Saw/saw-script/bin.
```

If everything is installed correctly you should be able to run saw

```bash
cabal run saw
```

This should open the saw interactive session. It should show you a
pretty SAW logo with the version number. We will learn more about the
interactive session later. For now you can quit the session with `:quit` or
`:q` like so:

```bash
sawscript> :quit
```

### Build the Coq backend for Saw

In this tutorial we will also interact with Heapster's Coq output. So
you'll need to follow the instructions in the
[README](../../../saw-core-coq/README.md) in the `saw-core-coq`
subdirectory.  Specifically, after installing the dependencies, you
will need to run the following (from the top level directory):

```bash
cd saw-core-coq/coq
make
```

It is expected that you will see a large number of warnings, but the
build should complete without any errors.

**TODO: How do we check if this is properly installed before continuing?**

For the sake of this tutorial, it will also be useful to install a
[user interface](https://coq.inria.fr/user-interfaces.html) to
interact with extracted Coq code. I recomment installing [Proof
General](https://proofgeneral.github.io/).

Before continuing, return to the top-level directory with `cd ../..`.

### Build all the examples

The easiest way to verify that everything has been set up correctly is
to build all the heapser examples. Simply go to the examples folder
and build, like so

```bash
cd /heapster-saw/examples
make
```

If this is the first time you run make in this folder, you will see `cabal run saw` called multiple times like so

```
/Path/To/Saw/
[16:59:41.084] Loading file "/Path/To/Saw/saw-script/heapster-saw/examples/linked_list.saw"
cabal run saw xor_swap.saw
Up to date



[16:59:42.974] Loading file "/Path/To/Saw/saw-script/heapster-saw/examples/xor_swap.saw"
cabal run saw xor_swap_rust.saw
Up to date
```

Eventually it should start making the coq files

```bash
COQC global_var_gen.v
COQC global_var_proofs.v
COQC sha512_gen.v
```

It might take several minutes but it should complete without any
errors. Once it's done, you know you are ready to use Heapster!

Before continuing, return to the top-level directory with `cd ../..`.

## A quick tour of SAW

You don't need to be an expert in SAW to handle Heapster, but a little
familiarity is useful. If you want to dig deeper into SAW, there is a
dedicated [tutorial](https://saw.galois.com/tutorial.html) for
that. Here we just present the general ideas of SAW.

### Overview

SAWScript is a special-purpose programming language developed by
Galois to help orchestrate and track the results of the large
collection of proof tools necessary for analysis and verification of
complex software artifacts.

In this tutorial we will overview how to use SAW to prove the functional
equality of different implementations. The steps are as follows:

- [1. Compile the code.](#1-compile-the-code)
- [2. Run the saw interpreter](#2-run-the-saw-interpreter)
- [3. Load the file and extract the two function specifications.](#3-load-the-file-and-extract-the-two-function-specifications)
- [4. Define the equality theorem.](#4-define-the-equality-theorem)
- [5. Call the SAT/SMT solver to prove the theorem.](#5-call-the-satsmt-solver-to-prove-the-theorem)

Steps 3-5 can all be written in a single `.saw` file, and batch processed by SAW.

### Running an example

We will use the same `ffs` example used in the [SAW
tutorial](https://saw.galois.com/tutorial.html). Head over to the
`saw-script/doc/tutorial/code` directory to find the file.

Our aim is to prove functional equivalence of two implementations of
`ffs` (there are more implementations in that file). The function
should return the index of the first non-zero bit of its input and
can be implemented in the following two ways.

```C
uint32_t ffs_ref(uint32_t word) {
    int i = 0;
    if(!word)
        return 0;
    for(int cnt = 0; cnt < 32; cnt++)
        if(((1 << i++) & word) != 0)
            return i;
    return 0; // notreached
}

uint32_t ffs_imp(uint32_t i) {
    char n = 1;
    if (!(i & 0xffff)) { n += 16; i >>= 16; }
    if (!(i & 0x00ff)) { n += 8;  i >>= 8; }
    if (!(i & 0x000f)) { n += 4;  i >>= 4; }
    if (!(i & 0x0003)) { n += 2;  i >>= 2; }
    return (i) ? (n+((i+1) & 0x01)) : 0;
}
```

The former loops over all the bits in the input until it finds the
first 1. The later does a binary search over the input by using masks
where there is a 1.

#### 1. Compile the code. 

   We can use clang to compile our C code down
   to LLVM like so:
   
   ```bash
   clang -g -c -emit-llvm -o ffs.bc ffs.c
   ```
   
   Where the options mean:
   * The `-g` flag instructs clang to include debugging information, which is useful in SAW to refer to variables and struct fields using the same names as in C.
   * The `-c` flag asks clang to only run the preprocess, compile, and assemble steps.
   * `-emit-llvm` requests LLVM bitcode as output.
   * `-o ffs.bc` tells clang to write the output into `ffs.bc`
   
Luckily, SAW has some code to do all of this for you in the `Makefile`. You can simply run 
```bash
> make ffs.bc
```
to get the same effect.

#### 2. Run the saw interpreter

Run `cabal run saw` to start the interpreter. You should see the SAW
logo and version number. Then you can run your first saw command:

   ```bash
   sawscript> print "Hello World"
   [14:49:30.413] Hello World
   ```

#### 3. Load the file and extract the two function specifications.
   To load the file, we will use `llvm_load_module`. We can check what the function does with 
   
   ```
   sawscript> :? llvm_load_module
   Description
   -----------
   
       llvm_load_module : String -> TopLevel LLVMModule
   
   Load an LLVM bitcode file and return a handle to it.
   ```
   
   Also, if you ever forget the name of a function, you can find it by
   running `:env` which will display the current sawscript
   environment. Finally you can always type `:help` to remember these
   commands.
   
   Run `l <- llvm_load_module "ffs.bc"` to load the file and store it
   in the variable `l`. If you print the environment with `:env` you
   will now see a new variable `l : LLVMModule`.
   
   Now from `l`, we want to extract the two functions
   
   ```
   sawscript> ffs_ref <- llvm_extract l "ffs_ref"
   sawscript> ffs_imp <- llvm_extract l "ffs_imp"
   ```
   
   That's it! If you want, you can check again `:env` to confirm the
   variables of type `Term` have been created.
   
#### 4. Define the equality theorem.
   
   Our theorem can now refer to the two recently created terms. Since
   we want to prove functional equivalence, we just state that the
   functions are equal for all inputs.
   
   ```
   sawscript> let thm1 = {{ \x -> ffs_ref x == ffs_imp x }};
   ```
   
   If you check the environment (`:env`) you will see that theorems are also of type `Term`.

#### 5. Call the SAT/SMT solver to prove the theorem.

Let's start by checking the command we will use `prove`:
	
```bash
sawscript> :? prove
Description
-----------

    prove : ProofScript () -> Term -> TopLevel ProofResult

Use the given proof script to attempt to prove that a term is valid
(true for all inputs). Returns a proof result that can be analyzed
with 'caseProofResult' to determine whether it represents a successful
proof or a counter-example.
```

Notice that it takes a `ProofScript`. You can look at the
environment (`:env`) and look at all the proof scripts (searching
for `ProofScript`), such as `abc`, `cvc4`, `mathsat`, and `z3`. If
you want to play with different solvers you would have to install
them. For now, since we have `z3` installed we can use it:

```bash
sawscript> result <- prove z3 thm1
sawscript> print result
[16:39:47.506] Valid
```

Which tells us that `z3` managed to prove the functional equality!

### Batch scripts

To make things easier, you can write all the code above into a single
`.saw` file and process it in a batch. The file `ffs.saw` would look like this:

```bash
print "Loading module ffs.bc";
l <- llvm_load_module "ffs.bc";

print "Extracting reference term: ffs_ref";
ffs_ref <- llvm_extract l "ffs_ref";

print "Extracting implementation term: ffs_imp";
ffs_imp <- llvm_extract l "ffs_imp";

print "Proving equivalence: ffs_ref == ffs_imp";
let thm1 = {{ \x -> ffs_ref x == ffs_imp x }};
result <- prove z3 thm1;
print result;

print "Done."
```

If you save the file in the same directory you can run:
```bash
% cabal run saw -- ffs.saw
Up to date

[16:49:13.646] Loading file "/PATH/TO/SAW/saw-script/doc/tutorial/code/my_ffs.saw"
[16:49:13.647] Loading module ffs.bc
[16:49:13.651] Extracting reference term: ffs_ref
[16:49:13.663] Extracting implementation term: ffs_imp
[16:49:13.666] Proving equivalence: ffs_ref == ffs_imp
[16:49:13.716] Valid
[16:49:13.716] Done.
```

That's it! You know the basics of SAW.

## Using Heapster

Heapster is, fundamentally, a type system for extracting functional
specifications from memory-safe imperative programs. The type system,
defined inside SAW, uses separation types to reason about memory
safety. Once a program is type-checked as memory-safe, it can be then
extracted as a functional program to be verified in Coq.

**TODO: Double check this description of Heapster**

This section assumes you are in the `/heapster-saw/examples`
directory. If you are not, make sure to go there

```bash
cd /heapster-saw/examples
make
```

### Heapster type-checking overview

Heapster allows us to (1) type check programs with respect to
types that can express separation loigc and (2) extract
the resulting functional program to Coq for further verification.

The process will generally involve


- [1. Generating LLVM bitcode](#1-generating-llvm-bitcode)
- [2. Run the SAW interpreter with Heapster](#2-run-the-saw-interpreter-with-heapster)
- [3. Load the file.](#3-load-the-file)
- [4. Writing heapster types for your functions](#4-writing-heapster-types-for-your-functions)
- [5. Type-check your program](#5-type-check-your-program)
- [6. Extract Coq specifications and write proofs](#6-writing-a-coq-file-to-prove-things-about-the-generated-functional-specifications)
				
Just like with SAW, Heapster can be processed in batch. To do so, you
can combine steps 2-6 in a `.saw` file and use SAW's batch processing.

### First example

This section will walk through the process of using Heapster to write,
typecheck and verify some C code. We will start by type-checking the
simple `add` function, wich you can find in `tutorial_c.c` in the
examples directory.

```C
uint64_t add (uint64_t x, uint64_t y) { return x + y; }
```

We will type-check the rest of the functions in that file, plus some
recursive functions later in the tutorial.


#### 1. Generating LLVM bitcode

Just like with SAW, we want to work with the LLVM bitcode
(`.bc`). 

```bash
clang -g -c -emit-llvm -o tutorial_c.bc tutorial_c.c
```

Alternatively, as long as you are in the `heapster-saw/examples` directory, you can also run 

```bash
make tutorial_c.bc
```

Be aware that the resulting bitcode may depend on your `clang` version
and your operating system. In turn, this means the Heapster commands
in your SAW script and the proofs in your Coq file may also be
dependent on how and where the bitcode is generated. If you find an
incompatibility, please report it. For all other examples beyond this
simple tutorial file, the binary code has been provided already to
avoid incompatibilities.

#### 2. Run the SAW interpreter with Heapster

We start by running saw with `cabal run saw`. Once SAW is loaded, you
can load all the Heapster commands with

```
sawscript> enable_experimental
```

If you print the environment now (with `:env`) you will notice a new
set of commands, all starting with `heapster_*`. You can also start
typing the name and press tab to see all the functions. These are all
the Heapster commands.

```
sawscript> heapster_ [TAB]
heapster_assume_fun                  heapster_find_symbols
heapster_assume_fun_multi            heapster_find_symbols_with_type
heapster_assume_fun_rename           heapster_find_trait_method_symbol
heapster_assume_fun_rename_prim      heapster_gen_block_perms_hint
heapster_block_entry_hint            heapster_get_cfg
heapster_define_irt_recursive_perm   heapster_init_env
heapster_define_irt_recursive_shape  heapster_init_env_debug
heapster_define_llvmshape            heapster_init_env_for_files
heapster_define_opaque_llvmshape     heapster_init_env_for_files_debug
heapster_define_opaque_perm          heapster_init_env_from_file
heapster_define_perm                 heapster_init_env_from_file_debug
heapster_define_reachability_perm    heapster_join_point_hint
heapster_define_recursive_perm       heapster_parse_test
heapster_define_rust_type            heapster_print_fun_trans
heapster_define_rust_type_qual       heapster_set_debug_level
heapster_export_coq                  heapster_set_translation_checks
heapster_find_symbol                 heapster_typecheck_fun
heapster_find_symbol_commands        heapster_typecheck_fun_rename
heapster_find_symbol_with_type       heapster_typecheck_mut_funs
```

You can then use `:?` to see further information for each of them.

#### 3. Load the file.

To load a file into heapster you can use `heapster_init_env`. Let's
check its documentation first

```
sawscript> :? heapster_init_env
Description
-----------

EXPERIMENTAL

    heapster_init_env : String -> String -> TopLevel HeapsterEnv

Create a new Heapster environment with the given SAW module name
 from the named LLVM bitcode file.
sawscript> 
```

As you see it takes two names. The second name refers to the bitcode
file containing the code we are verifying. The first is the name we
want to give our SAW core module. That is the place where Heapster
will store all our type checked functions and their extracted
functional specification. By convention we use the same name as the
LLVM file.

The function returns a Heapster environment that contains all the
definitions of the module (not to be confused with the SAW environment
that can be printed wiht `:env`).

```
env <- heapster_init_env "tutorial_c" "tutorial_c.bc"
```

we have created a new Heapster environment that we can explore. 

```
sawscript> env
[20:07:14.272] Module: tutorial_c.bc
Types:
  %struct.vector3d = type { i64, i64, i64 }

Globals:

External references:
  declare default void @llvm.dbg.declare(metadata, metadata,
                                         metadata)

Definitions:
  i64 @add(i64 %0, i64 %1)
  i64 @add_mistyped(i64 %0, i64 %1)
  void @incr_ptr(i64* %0)
  i64 @norm_vector(%struct.vector3d* %0)
```

The Heapster environment contains all the types, global definitions,
external references and functions from the loaded module. In our first
example we will focus on the `add` function. 


#### 4. Writing heapster types for your functions

The Heapster type for the `add` function is rather simple: 

```
"().arg0:int64<>, arg1:int64<> -o arg0:true, arg1:true, ret:int64<>"
```

It starts with an empty parenthesis `().` that contains the local
ghost environment. Since this function doesn't require ghost
variables, it is empty.

The rest of the type is composed of two parts separated by the linear
implication operator `-o`, sometimes known as "lollipop". The left hand
side of the operator, refers to the state of memory before the
function executes. And it says that the two arguments passed to `add`,
`arg0` and `arg1`, are 64-bit integers. The predicate `int64`, which
we will define in a moment, takes no arguments as represented by the
empty angled brackets `<>`.

The right hand side describes the memory after the function
executes. It says nothing about about the arguments (other than they
exist), with `true`, the predicate that is always satisfied. It also
says that the return value `ret` is another 64-bit integer.

Notice, in particular, that the type does not assert that the return
value is the sum of the inputs. That's because Hepaster is not a
correctness logic. It is a memory safety type system. However, as you
will shortly see, after checking for memory safety, we can extract
`add` as a functional program and verify its correctness in Coq.

##### Defining permission predicates

Before we tell Heapster the type of `add`, as described above, we
need to define the predicate `int64` with the following type 

```
exists x:bv 64.eq(llvmword(x))
```

It says that there exist some bit-vector of length 64 (`bv 64`) which
is equal, as an LLVM word, to the "current variable". In other words,
it says that the current variable is equal to some number that can be
described as a bit-vector of size 64.

To notify Heapster of this predicate we use the command
`heapster_define_perm`, which defines a new named permission which can
then be used in Heapster types. 

```
heapster_define_perm env "int64" " " "llvmptr 64" "exists x:bv 64.eq(llvmword(x))"
```

The first argument is the Heapster environment, the second is its
name, the third is its arguments (of which there are none), the fourth
is the type of value that the permission applies to, and the fifth is
its permision type. Notice how in Heapster, most of the arguments are
passed as strings. 

With this, the new permission is created and added to the
environment. Uses of this named permission are written `int64<>` where
the `<>` is the empty list of arguments, as seen in the type of `add`
above. Unfortunately, there is currently no way to print the newly defined
permissions. If you try to print the environment (`print env`) at this
point, you will only see the `llvm` definitions. We might add
functionality for showing permissions in the future.

#### 5. Type-check your program
   
Armed with the `int64` predicate, we can write the type for `add` and
ask Heapster to type check it.

```
heapster_typecheck_fun env "add" "().arg0:int64<>, arg1:int64<> -o arg0:true, arg1:true, ret:int64<>"
```

The `heapster_typecheck_fun` command takes the environment, the name
of the function to typecheck and its permission type. The command then
attempts to typecheck the function and extracts its functional
specification. The functional specification is then added to the SAW
core module `tutorial_c` with the sufix `__tuple_fun`, in this case
`add__tuple_fun`.

The function `add_mistyped`, in the same `tutorial_bc` and already
loaded in the Heapster environment, is identical to `add` so we can
experiment with mistyping. Try running the following command

```
heapster_typecheck_fun env "add_mistyped" "().arg0:true, arg1:int64<> -o arg0:true, arg1:true, ret:int64<>"
```

The first argument is typed as `true`, but we know it is an `i64`
which can't be proven from the trivial `true`. So this type check
should fail, but it silently terminates! What gives?

Heapster allows for the typechecker to fail in parts of
the function and the extraction will translate those parts into the
error specification. The user could then, for example, prove that
those locations are not reachable in the program, for full
correctness. Unfortunately, this means that the typechecking will fail
silently and an error won't be caught until we check the Coq
extraction, as we show in the next section.

#### 6. Writing a Coq file to prove things about the generated functional specification(s)

Once you're finished, use the following command to export all the
type-checked functions in the current environment as functional
specifications in Coq. By convention, we add a `_gen` suffix to the
filename.

```
heapster_export_coq env "tutorial_c_gen.v";
```

Open up the new `tutorial_c_gen.v` file in your examples
directory. You should see a handful of auto-generated imports and four
definitions.

The first two definitions `add__tuple_fun` and `add` might have a
scary looking types, but they simplify to

```
add__tuple_fun : (bitvector 64 -> bitvector 64 -> CompM (bitvector 64)) * unit
add : bitvector 64 -> bitvector 64 -> CompM (bitvector 64)
```

That is, `add__tuple_fun` if a list of definitions, encoded as a
tuple. Saw uses these heterogeneous lists to encode functions, or
parts of them, that depend on each other.  In this case, there is only
the `add` function and a unit `()`, representing the end of
the list (similar to `nil`).  The `add` function takes two integers
(as 64-bit vectors) and returns another one (under the `CompM` monoid
that accepts failure).

The other two definitions are the equivalent definitions for the
`add_mistyped` function. However, in `add_mistyped__tuple_fun` you
will find a call to `errorM` with an error message 

```
implUnfoldOrFail: Could not prove
  top_ptr1:true -o (). is_llvmptr
```

explaining that, for the first pointer (that is `arg0`) it couldn't
prove that `true -o (). is_llvmptr`, as we expected. The function
couldn't be typechecked with the given type.  The lack of calls to
`errorM` in `add__tuple_fun` confirms that it was correctly
typechecked.

Notice that the converse is not true: there are some well-typed
functions that will still use `errorM` in their extracted function to,
for example, dynamically check for memory bounds. We will see those
examples in later sections. **TODO: Make sure we do this. Perhaps add
an array example?**

Before we continue, make sure to build the `.vo` file, so we can
import the definitions in `tutorial_c_gen.v` from other files. Do so with 

```
make tutorial_c_gen.vo
```

This should produce a new file `tutorial_c_gen.vo`.


##### Writting your own proofs

Open a new coq file `tutorial_c_proofs.v` in the same folder
(i.e. `heapster-saw/examples/`) and the following preamble

```
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreScaffolding.
From CryptolToCoq Require Import SAWCoreVectorsAsCoqVectors.
From CryptolToCoq Require Import SAWCoreBitvectors.
From CryptolToCoq Require Import SAWCorePrelude.

(* The following 2 lines allows better automation *)
Require Import Examples.common.
Require Import Coq.Program.Tactics.

(* Import our function definitions*)
Require Import Examples.tutorial_c_gen.
Import tutorial_c.
```

It first imports all the SAW functionality we need and some useful
tactics. Then it imports our new definitions (e.g. `add`).

Our first proof will claim that the function `add` produces no
errors. More specifically, it says that for all inputs (that's what
`spec_refines_eq` quantifies) `add` always refines to `safety_spec`. That
is, it returns a pure value without errors.

```

Lemma no_errors_add (x y: bitvector 64) :
  spec_refines_eq (add x y) (safety_spec (x,y)).
Proof.
```

We will use our automation to quickly prove the lemma,

```
solve_trivial_spec 0 0. Qed.
```

You can also attempt the same proof with `add_mistyped`, which
obviously will fail, since `add_mistyped` has an error. First, you
will note that `add_mistyped` only takes one argument (since only one
was defined in its signature)

```
Lemma no_errors_add_mistyped (x: bitvector 64) :
  spec_refines_eq (add_mistyped x) (safety_spec (x)).
Proof. solve_trivial_spec 0 0.

	clarify_goal_tutorial.
```

After rewriting the terms for clarity, you can see the
remaining goal says that an `ErrorS` is a refinement of
`RetS`. In other words, it's trying to prove that a trivially
pure function has an error. That's obviously false.

```
Abort.
```

Congratulations you have written your first Coq proofs with Heapster!

### Pointers

The next function we will type-check is a simple function that
increments the value in a pointer

```C
void incr_ptr (uint64_t *x) { *x += 1; }
```

Assuming you completed the last section, you should have interactive
saw open, the `tutorial_c.bc` loaded in the environment `env`, so
`incr_ptr` should already be in your environment, but you can double
check by printing `env`. We can then skip the steps 1-3 and go
directly to writing heapster types for the function. 

The type for this function should be

```
(). arg0:ptr((W,0) |-> int64<>) -o arg0:ptr((W,0) |-> int64<>)
```

As before, the ghost environment is omitted and both sides of the
implication are identical, since the function doesn't change the shape
of memory. The return value is `void`, so we can omit it or add a
trivial `ret:true`.

The permission for pointers `ptr` takes three arguments. First, it
describes the read-write modality. In this case the
pointer is writable `W`, since it will be modified. The second
argument describes the pointer offset, here `0`. Finally, the third
argument describes the content of the pointer, in this case a 64-bit
integer `int64<>`.

Then we can type-check the function with

```
heapster_typecheck_fun env "incr_ptr" "(). arg0:ptr((W,0) |-> int64<>) -o arg0:ptr((W,0) |-> int64<>)"
```

Finally we can generate the functional specification in Coq with 

```
heapster_export_coq env "tutorial_c_gen.v";
```

The old file should be overwritten and now contains the functional
specification of `add`, `add_mistyped` and `incr_ptr`. As you can see
the definition of `incr_ptr__tuple_fun` has no references to `errorM`,
so we know it was correctly type checked.

You will have to generate the `.vo` again to write proofs about
`incr_ptr`. After you do so, we can easily prove that `incr_ptr`
produces no errors.

```
Lemma no_errors_incr_ptr (x: bitvector 64) :
  spec_refines_eq (incr_ptr x) (safety_spec x).
Proof.  solve_trivial_spec 0 0. Qed.
```

### Structs

The next function we will type-check deals with structs. In our
example, we defined a function that can compute the norm of a 3D
vector

``` C
// Struct that represents the three coordinates for a 3D vector
typedef struct { uint64_t x; uint64_t y; uint64_t z; } vector3d;

// function that computes the norm of a 3D vector
// || (x,y,z) || = x^2+y^2+z^2
uint64_t norm_vector (vector3d *v) { return (v->x * v->x + v->y * v->y + v->z * v->z); }
```

Again, we assume that you still have the definitions from the previous
sections so we can start defining the type for the function.

Let's start by defining a predicate for `vector3d` like so

```
heapster_define_perm env "vec3d" "rw:rwmodality" "llvmptr 64" "ptr((rw,0) |-> int64<>) * ptr((rw,8) |-> int64<>) * ptr((rw,16) |-> int64<>)"
```

First, notice that we added an arguments `rw` of type
`rwmodality`. This is such that we can control if the vector is
readable or writable. Second, notice that the predicate still applies
to 64-bit pointers. Finally, the type describes three integers, all
with the read-write modality given by the argument `rw`, at offsets
`0`, `8` and `16` and each with an `int64`.

Then we can define the type of `norm_vector` as

```
(). arg0:vec3d<R> -o arg0:vec3d<R>, ret:int64<>
```

which says that the function takes a readable 3D vector, and returns
an integer. Notice that the `arg0` on the right hand side could also
be written as `arg0:true`. However, we still want to express that the
function does change that memory so we make it explicit.

Then we can type-check the function with 

```
heapster_typecheck_fun env "norm_vector" "(). arg0:vec3d<R> -o arg0:vec3d<R>, ret:int64<>"
```

Finally we can generate the functional specification in Coq with 

```
heapster_export_coq env "tutorial_c_gen.v";
```

The functional specification of `norm_vector` should have been added
to the `tutorial_c_gen.v` file. You will have to generate the `.vo`
again to write proofs about `norm_vector`. After you do so, we can
easily prove that `norm_vector` produces no errors. The statement and
the proof, follow exactly the last two lemmas.

### Batch scripts

Notice that, just like in saw, Heapster scripts can be processed in
batch. You can create a file `tutorial_c.saw` with all the commands so
far. It should look something like this

```
enable_experimental
env <- heapster_init_env "tutorial_c" "tutorial_c.bc"
print "File loaded"

heapster_define_perm env "int64" " " "llvmptr 64" "exists x:bv 64.eq(llvmword(x))"
print "Defined an 64-bit integer."

heapster_typecheck_fun env "add" "().arg0:int64<>, arg1:int64<> -o arg0:true, arg1:true, ret:int64<>"
print "Type checked add."

heapster_typecheck_fun env "add_mistyped" "().arg0:true, arg1:int64<> -o arg0:true, arg1:true, ret:int64<>"
print "Type checked add_mistyped. This will produce an error in the output."

heapster_typecheck_fun env "incr_ptr" "(). arg0:ptr((W,0) |-> int64<>) -o arg0:ptr((W,0) |-> int64<>)"
print "Type checked incr_ptr."


heapster_define_perm env "vec3d" "rw:rwmodality" "llvmptr 64" "ptr((rw,0) |-> int64<>) * ptr((rw,8) |-> int64<>) * ptr((rw,16) |-> int64<>)"
heapster_typecheck_fun env "norm_vector" "(). arg0:vec3d<R> -o arg0:vec3d<R>, ret:int64<>"
print "Type checked incr_ptr."

heapster_export_coq env "tutorial_c_gen.v";
print "Export to Coq."

print "Done."
```

then you can process it with just

```
% cabal run saw -- tutorial_c.saw
Up to date



[16:41:49.222] Loading file "/Users/Santiago/Projects/saw-script/heapster-saw/examples/tutorial_c.saw"
[16:41:49.230] File loaded
[16:41:49.245] Type checked add.
[16:41:49.249] Type checked add_mistyped. This will produce an error in the output.
[16:41:49.257] Type checked incr_ptr.
[16:41:49.312] Type checked norm_vector.
[16:41:49.329] Export to Coq.
[16:41:49.329] Done.
```


### Arrays

We will briefly explore arrays, which have slightly more interesting
memory restrictions. Namely, array access must be in bounds. The code
in this section are already generated for you and you can find them,
together with more examples in the files `arrays.c`, `arrays.saw`,
`arrays_gen.v` and `arrays_proofs.v`.

We will consider the function `zero_array` which zeroes out all the
values in an array (see code in `arrays.c`).

```C
void zero_array (int64_t *arr, uint64_t len) {
  for (uint64_t i = 0; i < len; ++i) {
    arr[i] = 0;
  }
}
```

The type for this function is relatively simple, it only assumes that
`len` is actually the length for the given array `arr`. This is
achieved by used a shared or ghost variable `len` which is both the
length of the array and equal to the second argument (see the code in `arrays.saw`)

```
heapster_typecheck_fun env "zero_array"
  "(len:bv 64). arg0:int64array<len>, arg1:eq(llvmword(len)) -o \
              \ arg0:int64array<len>, arg1:true, ret:true";
```

Heapster also expects a loop invariant hint for every loop. Loop
invariants look just like function types, taking the loop variables as
arguments. In this case the loop introduces a new variable `i` which
is the offset into the array. We represent that with a new ghost
variable

```
heapster_typecheck_fun env "zero_array_from"
  "(len:bv 64, off:bv 64). arg0:int64array<len>, arg1:eq(llvmword(len)), arg2:eq(llvmword(off)) -o \
                         \ arg0:int64array<len>, arg1:true, arg2:true, ret:true";
```

Certainly function correctness must ensure that all the writes to the
array (i.e. `arr[i] = 0`) happen within bounds. However this is a
dynamic property which is not part of type-checking. Instead, Heapster
adds dynamic checks on the extracted code which we will see in the Coq
code. 

Let's go to `arrays_gen.v` (which has already been generated for you)
and look for the definition of `zero_array__bodies`. You will
notice that it calls `errorS` twice, but in this case, that's not a
sign of a typing error! Heapster includes these errors to catch
out-of-bounds array accesses and unrepresentable indices (i.e. index
that can't be written as a machine integer). The code below is a
simplification of the `zero_array__bodies` with some notation for
readability (see below for how to enable such pritty printing).

```
(fun (e0 : int64) (p0 : Vector int64 e0) =>
   CallS VoidEv emptyFunStack zero_array__frame
     (mkFrameCall zero_array__frame 1 e0 (0)[64] p0 tt tt tt),
  (fun (e0 e1 : int64) (p0 : Vector int64 e0) (_ _ _ : unit) =>
   if negb ((if e1 < e0 then (-1)[1] else (0)[1]) == (0)[1])
   then
    if ((17293822569102704640)[64] <= e1) && (e1 <= (1152921504606846975)[64])
    then
     If e1 <P e0
     Then CallS VoidEv emptyFunStack zero_array__frame
            (mkFrameCall zero_array__frame 1 e0 (e1 + (1)[64]) 
               (p0 [e1 <- (0)[64]]) tt tt tt)
     Else ErrorS (Vector int64 e0) "ghost_bv <u top_bv"
    else ErrorS (Vector int64 e0) "Failed Assert at arrays.c:61:5"
   else RetS p0, tt))
```
 
Notice there are two functions, the outermost one represents
`zero_array` and the one inside represents the loop. in the latter,
the arguments `e0`, `e1` and `p1` correspond to the length `len`, the
offset `i`, and the array `arr`. Notice most of that the function
performs several tests before executing any computation. The first two
tests, which are within `if then else` blocks, check that the offset
is less than the array length `e1 < e0`, and that the index `i` is
within the bounds of machine integers. The former is part of the loop
condition, the second is added by Heapster to ensure the ghost
variable represents a machine integer.

The last check, which is within uppercase `If Then Else` (which
handles option types) is not part of the original function but
inserted by Heapster. It checks that the array access is within bounds
`e1 <P e0`. The operator `<P` returns an optional proof of the array
access being safe. If the check fails, the function reports a runtime
error `ErrorS _ "ghost_bv <u top_bv"`.

If all the checks pass, then the function simply calls
itself recursively, with the next index and array with a new entry zeroed out.

```
(mkFrameCall zero_array__frame 1 e0 (e1 + (1)[64]) 
               (p0 [e1 <- (0)[64]]) tt tt tt)
```

The extra `tt` are artifacts that get inserted by Heapster, but you
can ignore them.

**Pritty printing:** you can enable this pretty printing by adding
`Import CompMExtraNotation. Open Scope fun_syntax.` after the files
imports. Then, after processing the file you can write `Print
zero_array__tuple_fun`, after the function has been defined, and you
should see the pretty printed version appear in the response. You
don't really modify `arrays_gen.v` so you can do this exploration in
`arrays_proofs.v` or just remember to clean up `arrays_gen.v` after
you are done.


We shall now prove that this function in fact should never return an
error if the inputs are correct. Go to `array_proofs.v` and look at the proof 

```
Lemma no_errors_zero_array x y:
  spec_refines_eq (zero_array x y)
    (total_spec (fun '(len, vec, dec) =>  zero_array_precond len) (fun _ _ => True) (x,y, bvAdd _ x (intToBv _ 1))).
Proof.
```

It claims that, assuming the precondition `zero_array_precond` is
satisfied, then the function `zero_array` produces no errors. The
precondition simply says that the length of the array is within
computable integers.

```
Definition zero_array_precond x
  := 64 <= x /\ x <= bvMem_hi.
```


We will not go into detail about the proof, but notice that the
important steps are handled by custom automation. 


### Recursive data structures

We will now typecheck a function over lists, a recursive data
structure. You can start a fresh SAW session with `cabal run saw`
(quit any current session with `:q` if you are in one), but make sure
you do so from the `heapster-saw/examples` directory.

Specifically, we want to verify the function `is_elem`,
which tests if a specific value is in a list. The function, together
with others, can be found in `linked_list.c`, in the examples
directory.

```C
typedef struct list64_t {
  int64_t data;
  struct list64_t *next;
} list64_t;

int64_t is_elem (int64_t x, list64_t *l) {
  if (l == NULL) {
    return 0;
  } else if (l->data == x) {
    return 1;
  } else {
    return is_elem (x, l->next);
  }
}
```

#### 1. Generating LLVM bitcode

We have already included the binary for all the examples, but if you
want to generate it yourself, you can run

```bash
make linked_list.bc
```

#### 2. Run the SAW interpreter with Heapster

Load the Heapster commands

```bash
sawscript> enable_experimental
```

#### 3. Load the file and extract the function types.

To work with lists, we need add the SAW core definition of lists to
our SAW core module. The definition is 

```
List_def : (a:sort 0) -> sort 0;
List_def a = List a;
```

**TODO: what is this definition? Why can't we just use `List a`**

We can add such definitions to a SAW core file. One has already been
created for you at `linked_list.sawcore`. Every SAW core file starts
with the declaration of the module name and, most files, import the
Prelude.

```
module linked_list where

import Prelude;
```

With this file created, we start our environment with

```
env <- heapster_init_env_from_file "linked_list.sawcore" "linked_list.bc";
```

which, much like `heapster_init_env`, creates a new environment but,
instead of creating a fresh SAW core module, it initialises the module
with the given file, here `linked_list.sawcore`. Just as before, this
creates a new Heapster environment that we can explore.

```
sawscript> print env
[20:19:48.436] Module: linked_list.bc
Types:
  %struct.list64_t = type { i64, %struct.list64_t* }

Globals:

External references:
  declare default void @llvm.dbg.declare(metadata, metadata,
                                         metadata)
  declare default i8* @malloc(i64)

Definitions:
  i64 @is_head(i64 %0, %struct.list64_t* %1)
  i64 @is_elem(i64 %0, %struct.list64_t* %1)
  i64 @any(i64(i64)* %0, %struct.list64_t* %1)
  %struct.list64_t* @find_elem(i64 %0, %struct.list64_t* %1)
  %struct.list64_t* @sorted_insert(i64 %0, %struct.list64_t* %1)
  %struct.list64_t* @sorted_insert_no_malloc(%struct.list64_t* %0,
                                             %struct.list64_t* %1)
```

#### 4. Writing heapster types for your functions

We can check in the environment `env` for the LLVM type of the function we
are type checking. 

```LLVM
i64 @is_elem(i64 %0, %struct.list64_t* %1)
```

The function `is_elem` takes a 64-bit integer and a list of 64-bit
integers, and returns another 64-bit integer. After the return, we
don't care about the inputs, so we can write the type like this

```
().arg0:int64<>, arg1:List64<R> -o arg0:true, arg1:true, ret:int64<>
```

But we will need to define the predicates for `int64` and `List64`

##### Defining list permissions

We know how to define `int64`, as we did before, 

```
sawscript> heapster_define_perm env "int64" " " "llvmptr 64" "exists x:bv 64.eq(llvmword(x))"
```

but we need a new predicate for lists.  Before we look at the
definition of a `List64<rw>` lets focus on its permission type. First
of all, `List64<rw>` takes a single argument `rw:rwmodality` which
determines if the list is readable or writable, just like 3D
vectors. It's type should look something like this

```
["eq(llvmword(0))", "ptr((rw,0) |-> int64<>) * ptr((rw,8) |-> List64<rw>)"]
```

The definition shows the diferent cases for a list, separated by a
comma. In the first case, a `List64` can be a null pointer, expressed
with the type `eq(llvmword(0))`. In the second case, a list is a
pointer where offset `0` is the head, an `Int64`, and offset `8` is
the tail, is recursively a `List64<rw>`. In the later case,
both elements are tagged with `rw`, describing if they are readable or
writable, as determined by the argument to `List64<rw>`.

To define [permissions](doc/Permissions.md) which can describe
unbounded data structures, you can use the
`heapster_define_recursive_perm` command. Here is how to use the
command to define lists.

```
heapster_define_recursive_perm
  env
  "List64"
  "rw:rwmodality"
  "llvmptr 64"
  ["eq(llvmword(0))", "ptr((rw,0) |-> int64<>) * ptr((rw,8) |-> List64<rw>)"]
  "List_def" "foldList" "unfoldList";
```

Its first four arguments are the same as for `heapster_define_perm`,
namely the environment, the name, the arguments and the type of value
that the permission applies to. The fifth argument is its permission
type. The final three arguments are its translation into SAW core. As
you might remember, this is the `List_def` we defined in our SAW core
file which is now loaded in the module. The other two `foldList` and
`unfoldList` are **TODO: What are these???**

See this [additional documentation](../Permissions.md) for a
reference on the syntax and meaning of heapster permissions.

#### 5. Type-check your program
   
Just as before you only need to run

``` 
heapster_typecheck_fun env "is_elem"
"().arg0:int64<>, arg1:List64<R> -o arg0:true, arg1:true,
ret:int64<>"; 
``` 

Note that for more complicated examples, usually examples involving loops,
the `heapster_block_entry_hint` command will also need to be used in order for
the `heapster_typecheck_fun` command to succeed. In the case of functions with
loops, this hint corresponds to a loop invariant. Additionally, such examples
will also often require your unbounded data structure to be defined as a
reachability permission, using `heapster_define_reachability_perm`, instead of
just as a recursive permission. See `iter_linked_list.saw` for some
examples of using the commands mentioned in this paragraph.

Once you're finished, use the following command to export all the type-checked
functions in the current environment as functional specifications in Coq. By
convention, we add a `_gen` suffix to the filename.
```
heapster_export_coq env "my_file_gen.v";
```
