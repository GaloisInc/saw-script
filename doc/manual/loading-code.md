# Loading Code

The first step in analyzing any code is to load it into the system.

## Loading LLVM

To load LLVM code, simply provide the location of a valid bitcode file
to the `llvm_load_module` function.

* `llvm_load_module : String -> TopLevel LLVMModule`

The resulting `LLVMModule` can be passed into the various functions
described below to perform analysis of specific LLVM functions.

The LLVM bitcode parser should generally work with LLVM versions between
3.5 and 16.0, though it may be incomplete for some versions. Debug
metadata has changed somewhat throughout that version range, so is the
most likely case of incompleteness. We aim to support every version
after 3.5, however, so report any parsing failures as [on
GitHub](https://github.com/GaloisInc/saw-script/issues).

## Loading Java

Loading Java code is slightly more complex, because of the more
structured nature of Java packages. First, when running `saw`, three flags
control where to look for classes:

* The `-b` flag takes the path where the `java` executable lives, which is used
  to locate the Java standard library classes and add them to the class
  database. Alternatively, one can put the directory where `java` lives on the
  `PATH`, which SAW will search if `-b` is not set.

* The `-j` flag takes the name of a JAR file as an argument and adds the
  contents of that file to the class database.

* The `-c` flag takes the name of a directory as an argument and adds all class
  files found in that directory (and its subdirectories) to the class database.
  By default, the current directory is included in the class path.

Most Java programs will only require setting the `-b` flag (or the `PATH`), as
that is enough to bring in the standard Java libraries. Note that when
searching the `PATH`, SAW makes assumptions about where the standard library
classes live. These assumptions are likely to hold on JDK 7 or later, but they
may not hold on older JDKs on certain operating systems. If you are using an
old version of the JDK and SAW is unable to find a standard Java class, you may
need to specify the location of the standard classes' JAR file with the `-j`
flag (or, alternatively, with the `SAW_JDK_JAR` environment variable).

Once the class path is configured, you can pass the name of a class to
the `java_load_class` function.

* `java_load_class : String -> TopLevel JavaClass`

The resulting `JavaClass` can be passed into the various functions
described below to perform analysis of specific Java methods.

Java class files from any JDK newer than version 6 should work. However,
support for JDK 9 and later is experimental. Verifying code that only uses
primitive data types is known to work well, but there are some as-of-yet
unresolved issues in verifying code involving classes such as `String`. For
more information on these issues, refer to
[this GitHub issue](https://github.com/GaloisInc/crucible/issues/641).

## Loading MIR

To load a piece of Rust code, first compile it to a MIR JSON file, as described
in [this section](#compiling-mir), and then provide the location of the JSON
file to the `mir_load_module` function:

* `mir_load_module : String -> TopLevel MIRModule`

SAW currently supports Rust code that can be built with a [January 23, 2023
Rust nightly](https://static.rust-lang.org/dist/2023-01-23/).  If you encounter
a Rust feature that SAW does not support, please report it [on
GitHub](https://github.com/GaloisInc/saw-script/issues).

## Notes on Compiling Code for SAW

SAW will generally be able to load arbitrary LLVM bitcode, JVM bytecode, and
MIR JSON files, but several guidelines can help make verification easier or
more likely to succeed.

### Compiling LLVM

For generating LLVM with `clang`, it can be helpful to:

* Turn on debugging symbols with `-g` so that SAW can find source
  locations of functions, names of variables, etc.

* Optimize with `-O1` so that the generated bitcode more closely matches
  the C/C++ source, making the results more comprehensible.

* Use `-fno-threadsafe-statics` to prevent `clang` from emitting
  unnecessary pthread code.

* Link all relevant bitcode with `llvm-link` (including, *e.g.*, the C++
  standard library when analyzing C++ code).

All SAW proofs include side conditions to rule out undefined behavior,
and proofs will only succeed if all of these side conditions have been
discharged. However the default SAW notion of undefined behavior is with
respect to the semantics of LLVM, rather than C or C++. If you want to
rule out undefined behavior according to the C or C++ standards,
consider compiling your code with `-fsanitize=undefined` or one of the
related flags[^1] to `clang`.

Generally, you'll also want to use `-fsanitize-trap=undefined`, or one
of the related flags, to cause the compiled code to use `llvm.trap` to
indicate the presence of undefined behavior. Otherwise, the compiled
code will call a separate function, such as
`__ubsan_handle_shift_out_of_bounds`, for each type of undefined
behavior, and SAW currently does not have built in support for these
functions (though you could manually create overrides for them in a
verification script).

[^1]: https://clang.llvm.org/docs/UsersManual.html#controlling-code-generation

### Compiling Java

For Java, the only compilation flag that tends to be valuable is `-g` to
retain information about the names of function arguments and local
variables.

### Compiling MIR

In order to verify Rust code, SAW analyzes Rust's MIR (mid-level intermediate
representation) language. In particular, SAW analyzes a particular form of MIR
that the [`mir-json`](https://github.com/GaloisInc/mir-json) tool produces. You
will need to intall `mir-json` and run it on Rust code in order to produce MIR
JSON files that SAW can load (see [this section](#loading-mir)). You will also
need to use `mir-json` to build custom versions of the Rust standard libraries
that are more suited to verification purposes.

If you are working from a checkout of the `saw-script` repo, you can install
the `mir-json` tool and the custom Rust standard libraries by performing the
following steps:

1. Clone the [`crucible`](https://github.com/GaloisInc/crucible) and `mir-json`
   submodules like so:

   ```
   $ git submodule update deps/crucible deps/mir-json
   ```

2. Navigate to the `mir-json` submodule:

   ```
   $ cd deps/mir-json
   ```

3. Follow the instructions laid out in the [`mir-json` installation
   instructions](https://github.com/GaloisInc/mir-json#installation-instructions)
   in order to install `mir-json`.

4. Navigate to the
   [`crux-mir`](https://github.com/GaloisInc/crucible/tree/master/crux-mir)
   subdirectory of the `crucible` submodule:

   ```
   $ cd ../crucible/crux-mir/
   ```

5. Run the `translate_libs.sh` script:

   ```
   $ ./translate_libs.sh
   ```

   This will compile the custom versions of the Rust standard libraries using
   `mir-json`, placing the results under the `rlibs` subdirectory.

6. Finally, define a `SAW_RUST_LIBRARY_PATH` environment variable that points
   to the newly created `rlibs` subdirectory:

   ```
   $ export SAW_RUST_LIBRARY_PATH=<...>/crucible/crux-mir/rlibs
   ```

For `cargo`-based projects, `mir-json` provides a `cargo` subcommand called
`cargo saw-build` that builds a JSON file suitable for use with SAW. `cargo
saw-build` integrates directly with `cargo`, so you can pass flags to it like
any other `cargo` subcommand. For example:

```
# Make sure that SAW_RUST_LIBRARY_PATH is defined, as described above
$ cargo saw-build <other cargo flags>
<snip>
linking 11 mir files into <...>/example-364cf2df365c7055.linked-mir.json
<snip>
```

Note that:

* The full output of `cargo saw-build` here is omitted. The important part is
  the `.linked-mir.json` file that appears after `linking X mir files into`, as
  that is the JSON file that must be loaded with SAW.
* `SAW_RUST_LIBRARY_PATH` should point to the the MIR JSON files for the Rust
  standard library.

`mir-json` also supports compiling individual `.rs` files through `mir-json`'s
`saw-rustc` command. As the name suggests, it accepts all of the flags that
`rustc` accepts. For example:

```
# Make sure that SAW_RUST_LIBRARY_PATH is defined, as described above
$ saw-rustc example.rs <other rustc flags>
<snip>
linking 11 mir files into <...>/example.linked-mir.json
<snip>
```

## Notes on C++ Analysis

The distance between C++ code and LLVM is greater than between C and
LLVM, so some additional considerations come into play when analyzing
C++ code with SAW.

The first key issue is that the C++ standard library is large and
complex, and tends to be widely used by C++ applications. To analyze
most C++ code, it will be necessary to link your code with a version of
the `libc++` library[^2] compiled to LLVM bitcode. The `wllvm` program
can[^3] be useful for this.

The C++ standard library includes a number of key global variables, and
any code that touches them will require that they be initialized using
`llvm_alloc_global`.

Many C++ names are slightly awkward to deal with in SAW. They may be
mangled relative to the text that appears in the C++ source code. SAW
currently only understands the mangled names. The `llvm-nm` program can
be used to show the list of symbols in an LLVM bitcode file, and the
`c++filt` program can be used to demangle them, which can help in
identifying the symbol you want to refer to. In addition, C++ names from
namespaces can sometimes include quote marks in their LLVM encoding. For
example:

~~~~
%"class.quux::Foo" = type { i32, i32 }
~~~~

This can be mentioned in SAW by saying:

~~~~
llvm_type "%\"class.quux::Foo\""
~~~~

Finally, there is no support for calling constructors in specifications,
so you will need to construct objects piece-by-piece using, *e.g.*,
`llvm_alloc` and `llvm_points_to`.

[^2]: https://libcxx.llvm.org/docs/BuildingLibcxx.html
[^3]: https://github.com/travitch/whole-program-llvm
