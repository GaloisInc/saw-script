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
        - [Overview](#overview-1)
        - [Running an example](#running-an-example-1)
            - [1. Generating LLVM bitcode](#1-generating-llvm-bitcode)
            - [2. Run the SAW interpreter with Heapster](#2-run-the-saw-interpreter-with-heapster)
            - [3. Load the file and extract the two function specifications.](#3-load-the-file-and-extract-the-two-function-specifications-1)
            - [4. Writing heapster specifications for your functions](#4-writing-heapster-specifications-for-your-functions)
                - [Pen and paper specification](#pen-and-paper-specification)
                - [Defining permission predicates](#defining-permission-predicates)
            - [5. Writing a SAW script to type-check your code with respect to the sepcification](#5-writing-a-saw-script-to-type-check-your-code-with-respect-to-the-sepcification)
            - [6. Writing a Coq file to prove things about the generated functional specification(s)](#6-writing-a-coq-file-to-prove-things-about-the-generated-functional-specifications)
    - [Looking under the hood](#looking-under-the-hood)
        - [Heapster commands and environments](#heapster-commands-and-environments)
        - [Permissions](#permissions)
        - [Type-checking](#type-checking)

<!-- markdown-toc end -->


## Building

We'll start by building everything you need to use Heapster. All the
commands here are with respect to the top-level saw-script directory.

### Build Saw 

You will need to follow the instructions in the top-level README to
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

In this tutorial we will also interact with Heapster's Coq output. So you'll need
to follow the instructions in the README in the `saw-core-coq` subdirectory.
Specifically, after installing the dependencies, you will need to run the
following (from this directory):
```bash
cd /saw-core-coq/coq
make
```

It is expected that you will see a large number of warnings, but the
build should complete without any errors.

**TODO: How do we check if this is properly installed before continuing?**

Before continuing, return to the top-level directory with `cd ..`.

### Build all the examples

The easiest way to verify that everything has been set up correctly is
to build all the heapser examples. Simply go to the examples folder
and build, like so

```bash
cd /heapster-saw/examples
make
```
You will see several files build that looks like this:
```bash
COQC global_var_gen.v
COQC global_var_proofs.v
COQC sha512_gen.v
```

It will take several minutes and it should complete without any
errors. Once it's done, you know you are ready to use Heapser!

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

In this tutorial we will overview how to use SAW to proof functional
equality different implementations. The steps are as follows:

1. Compile the code down to llvm bitecode (i.e. `.bc` files)
2. Run the saw interpreter
3. Load the file and extract the two function specifications.
4. Define the equality theorem. 
5. Call the SAT/SMT solver to prove the theorem.

Steps 3-5 can all be written in a single `.saw` file, and batch processed by SAW.

### Running an example

We will use the same `ffs` example used in the [SAW
tutorial](https://saw.galois.com/tutorial.html). Head over to the
`saw-script/doc/tutorial/code` directory to find the file.

Our aim is to prove functional equivalence of two implementatinos fo
`ffs` (there are more implementations in that file). The function is
should return the index of the first non-zero bit of it's input and
can be implemented in the follwoing two ways.

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
   * The `-c` flag asks clang to only run preprocess, compile, and assemble steps.
   * `-emit-llvm` requests llvm bitecode as output.
   * `-o ffs.bc` tells clang to write the output into `ffs.bc`
   
Luckily, SAW has some code to do all of this for you in the `Makefile`. You can simply run 
```bash
> make ffs.bc
```
to get the same effect.

#### 2. Run the saw interpreter

Run `cabal run saw` to start the interpreter. You should see the SAW
logo and version number. Then you cna run your first saw command:

   ```bash
   sawscript> print "Hello World"
   [14:49:30.413] Hello World
   ```

#### 3. Load the file and extract the two function specifications.
   To load the file, we will use `llvm_load_module`. We can check what the function does with 
   
   ``` bash
   sawscript> :? llvm_load_module
   Description
   -----------
   
       llvm_load_module : String -> TopLevel LLVMModule
   
   Load an LLVM bitcode file and return a handle to it.
   ```
   
   Also, if you ever forget the name of a function, you cna find it by
   running `:env` which will display the current sawscript
   environment. Finally you can allways type `:help` to remember these
   commands.
   
   So, run `l <- llvm_load_module "ffs.bc"` to load the file and stored in variable `l`. If you print the environment with `:env` you will now see a new variable `l : LLVMModule`.
   
   Now from `l`, we want to extract the two functions
   
   ```
   sawscript> ffs_ref <- llvm_extract l "ffs_ref"
   sawscript> ffs_imp <- llvm_extract l "ffs_imp"
   ```
   
   That's it! If you want, you can check again `:env` to confirm the
   variables of type `Term` have been created.
   
#### 4. Define the equality theorem.
   
   Our theorem can now refer to the two recently created terms. since
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
them. For now, since we have `z3` installed we can call.

```bash
sawscript> result <- prove z3 thm1
sawscript> print result
[16:39:47.506] Valid
```

Which tells us that z3 managed to prove the functional equality!

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

Heapster is a, fundamentally, a type system for extracting functional
specifications from memory-safe imperative programs. The type system,
defined inside SAW, uses separation types to reason about memory
safety. Once a program is type-checked as memory-safe, it can be then
extracted as a functional program to be verified in Coq.

**TODO: Double check this description of Heapster**

### Overview

Heapster allows us to (1) type check programs with respect to
types/specifications that can express separation loigc and (2) extract
the resulting functional program to Coq for further verification.

The process will generally involve

1. Generating LLVM bitcode from your file
2. Run the saw interpreter with Heapster
3. Load the file and extract the functions.
4. Writing heapster specifications for your functions
5. Writing a SAW script to type-check your code with respect to the
   sepcification, and
6. Writing a Coq file to prove things about the generated functional
   specification(s).

Just like with SAW, Heapster can be processed in batch. To do so, you
can combine steps 2-6 in a `.saw` file and use SAW's batch processing.

### Running an example

This section will walk through the process of using Heapster to write
and verify some C code. Specifially, we want to verify the function
`is_elem`, which tests if a specific value is in a list. The function,
together with others, can be found in `examples/linked_list.c`.

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

Just like with SAW, we want to work with the LLVM bitcode (`.bc`), so
you can generate it just like before. Note that we have already
included the binary for all the examples so you don't really need to
run this command.

   ```bash
   clang -g -c -emit-llvm -o ffs.bc ffs.c
   ```

(The alternative command `make examples/linked_list.bc` won't work
because the shorcut is not defined in the Makefile of heapster.)

Be aware that the resulting bitcode may depend on your `clang` version and your
operating system. In turn, this means the Heapster commands in your SAW script
and the proofs in your Coq file may also be dependent on how and where the
bitcode is generated. If you find an incompatibility, please report it.

#### 2. Run the SAW interpreter with Heapster

We start by running saw with `cabal run saw`. Once SAW is loaded, you
can load all the Heapster commands with

   ```bash
   sawscript> enable_experimental
   ```

If you print the environment now (wiht `:env`) you will notice a new
set of commands, all starting with `heapster_*`. You can also start
typing the name and press tab to see all the functions those are all the Heapster commands.

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


#### 3. Load the file and extract the two function specifications.

To load a file into heapster you can use `heapster_init_env`. Let's
check it's documentation first

``` bash
sawscript> :help heapster_init_env
Description
-----------

EXPERIMENTAL

heapster_init_env : String -> String -> TopLevel HeapsterEnv

Create a new Heapster environment with the given SAW module name
from the named LLVM bitcode file.
```

As you see it takes two names. The first, is the name of the SAW core
module where Heapster will write all the specifications we extract. If
you start with a fresh name, Heapster will autogenerate a new module
for you. We will see later how to use existisng modules. The second
name referse to the bitecode file containing the code we are
verifying.

The function returns a Heapster environment that contains all the
definitions of the module (not to be confused with the SAW environment
that can be printed wiht `:env`).

Let's load our module with

```
env <- heapster_init_env "linked_list" "examples/linked_list.bc";
```

we have created a new Heapster environment that we can explore. 

```
sawscript> print env
[20:19:48.436] Module: examples/linked_list.bc
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

The heapster environment contains all the types, global definitions,
external references and functions from the loaded module.


#### 4. Writing heapster specifications for your functions

##### Pen and paper specification

Before we go foward using Heapster, let's think about what the
specification for `is_elem` should be. As we can check in the
environment `env`, `is_elem` takes a 64-bit integer the "element".

```LLVM
i64 @is_elem(i64 %0, %struct.list64_t* %1)
```

Hence, precondition to the function should reflect these two inputs
like so `arg0:int64, arg1: list int64`, for some predicates `int64`
and `list` that express a single integer and a list of them.

Moreover, the function returns a new i64-bit integer and, as we can
see in the code of `is_elem`, the arguments are not modified. So the
postcondition, of the function could be described by `arg0:int64,
arg1: list int64, ret:int64`. Alternatively, if we don't care about
the inputs after the call we can simplify it to `arg0:true, arg1:
true, ret:int64`, where `true` is a predicate the is always satisfied.
 
Then, using the linear implication `-o` we can express the
specification of `is_elem` as

```
arg0:int64, arg1: list int64 -o arg0:true, arg1:true, ret:int64
```

Notice that this is a memory-safety specification, not a correctness
predicate. We can reason about the correctness of the function once we
extract it as a functional program in Coq.

In the next sections, we shall define the predicates necessary to
write this specification in Heapster.

##### Defining permission predicates

One of the simplest Heapster commands is `heapster_define_perm`, which defines
a new named permission which can then be used in Heapster types. As an
example, the following defines the permission which describes a 64-bit integer
value:

```
heapster_define_perm env "int64" " " "llvmptr 64" "exists x:bv 64.eq(llvmword(x))"
```

The first argument is the Heapster environment, the second is its
name, the third is its arguments (of which there are none), the fourth
is the type of value that the permission applies to, and the fifth is
its definition. the new permission is created and added to the
environment. **TODO: Can I print the new permission? `print env` does
not show new permission definintions.**

The permission predicate for lists is a little more complicated
because it requires a recursive definition. To define
[permissions](doc/Permissions.md) which can describe unbounded data
structures, you can use the `heapster_define_recursive_perm`
command. As an example, here is how to describe a linked list of
64-bit words using this command:

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

Its first four arguments are the same as for `heapster_define_perm`,
its fifth argument contains its different inductive cases (in this
case, a `List64` is either a null pointer, or a pointer to an `Int64`
and another `List64`), and its final three arguments are its
translation into SAW core. Here the SAW core definitions used are from
the SAW core prelude which are included by default when Heapster
autogenerates a a module for you. If you need new SAW core
definitions, you will need to use the following command instead of
`heapster_init_env`:

```
env <- heapster_init_env_from_file "my_file.sawcore" "my_file.bc";
```

See this [additional documentation](doc/Permissions.md) for a
reference on the syntax and meaning of heapster permissions.

#### 5. Writing a SAW script to type-check your code with respect to the sepcification
   
We begin by converting the pen-and-paper specification of `is_elem`
into a Heapster specification. First, every heapster type begins with
the declaration of a ghost environment. Our specification doesn't use
any ghost variable so that is `().` Moreover, for every predicate we
use, we must specify whether the location is readble-only `<R>` or
both readable and writable `<>`. Whith this we can write our specification as 

```
().arg0:int64<>, arg1:List64<R> -o arg0:true, arg1:true,
ret:int64<>
```
   
Finally, to actually type-check a function you can use
`heapster_typecheck_fun`. That takes the environment, the name of the
function to type-check and the type, like so

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
just as a recursive permission. See `examples/iter_linked_list.saw` for some
examples of using the commands mentioned in this paragraph.

Once you're finished, use the following command to export all the type-checked
functions in the current environment as functional specifications in Coq. By
convention, we add a `_gen` suffix to the filename.
```
heapster_export_coq env "my_file_gen.v";
```

#### 6. Writing a Coq file to prove things about the generated functional specification(s)

**TODO**

## Looking under the hood

### Heapster commands and environments

### Permissions

### Type-checking
