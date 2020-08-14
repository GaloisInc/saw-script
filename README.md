[![Build
Status](https://travis-ci.org/GaloisInc/saw-script.svg?branch=master)](https://travis-ci.org/GaloisInc/saw-script)

# SAWScript

This repository contains the code for SAWScript, the scripting
language that forms the primary user interface to the Software
Analysis Workbench (SAW). It provides the ability to reason about
formal models describing the denotation of programs written in
languages such as C, Java, and Cryptol.

## Documentation

The [SAWScript tutorial](https://saw.galois.com/tutorial.html) gives an
introduction to using the SAWScript interpreter. A longer
[manual](https://github.com/GaloisInc/saw-script/blob/master/doc/manual/manual.md)
describes the breadth of SAWScript's features.

## Precompiled Binaries

Precompiled SAWScript binaries for a variety of platforms are available on the [releases page](https://github.com/GaloisInc/saw-script/releases).

## Getting Z3

SAW can use many theorem provers, but because of its use of Cryptol it
always needs to have Microsoft Research's [Z3 SMT
solver](https://github.com/Z3Prover/z3) installed.  You can download Z3
binaries for a variety of platforms from their [releases
page](https://github.com/Z3Prover/z3/releases).

We currently recommend Z3 4.8.7. If you plan to use path satisfiability
checking, you'll also need Yices version 2.6.1 or newer.

After installation, make sure that `z3` (or `z3.exe` on Windows)
is on your PATH.

## Manual Installation

To build SAWScript and related utilities from source:

  * Ensure that you have the
    [Stack](https://github.com/commercialhaskell/stack) program on your
    `PATH`. If you don't already have Stack, then `cabal install stack`,
    or download a precompiled binary from
    https://github.com/commercialhaskell/stack/releases.

  * Ensure that you have the C libraries and header files for
    `terminfo`, which generally comes as part of `ncurses` on most
    platforms. On Fedora, it is part of the `ncurses-compat-libs` package.
    You will also need the C headers for `zlib`.

  * Ensure that you have the programs `javac` and `z3` on your
    `PATH`. Z3 binaries are available at
    https://github.com/Z3Prover/z3/releases

  * Setup a `stack.yaml` for your OS and preferred GHC.

    Choose one of the Stack YAML config files and link it to
    `stack.yaml`:

        ln -s stack.<ghc version and os>.yaml stack.yaml

    The `stack-<ghc version>-unix.yaml` files are for both Linux and
    OS X.

    (Alternatively, you can

        export STACK_YAML=stack.<ghc version and os>.yaml

    instead of creating a symlink.

    **Developers**: defining a `STACK_YAML` env var also overrides the
    `stack.yaml` file, if any, and so is useful for testing a
    alternative build without permanently changing your default. You
    can even define `STACK_YAML` only for the current command: e.g.

        STACK_YAML=stack.<ghc version and os>.yaml stack build

    will build SAWScript using the given Stack YAML.)

  * Build SAWScript by running

        ./build.sh

    The SAWScript executables will be created in

        echo `stack path --local-install-root`/bin

    a path under the SAWScript repo. You can install SAWScript into
    a more predictable location by running

        stack install

    which installs into

        stack path --local-bin-path

    which is `$HOME/.local/bin` by default.

  * Optionally, run ./stage.sh to create a binary tarball.

## Notes on LLVM

SAW can analyze LLVM programs (usually derived from C, but potentially
for other languages). The only tool strictly required for this is a
compiler that can generate LLVM bitcode, such as `clang`. However,
having the full LLVM tool suite available can be useful. We have tested
SAW with LLVM and `clang` versions from 3.5 to 9.0, as well as the
version of `clang` bundled with Apple Xcode. We welcome bug reports on
any failure to parse bitcode from LLVM versions in that range.

Note that successful parsing doesn't necessarily mean that verification
will be possible for all language constructs. There are various
instructions that are not supported during verification. However,
any failure during `llvm_load_module` should be considered a bug.

## Related Packages

Many dependencies are automatically downloaded into `deps/` when you
build using `build.sh`; see
[Manual Installation](#manual-installation) above. Key automatically
downloaded dependencies include:

* `deps/abcBridge/`:        [Haskell bindings for ABC](https://github.com/GaloisInc/abcBridge)
* `deps/crucible/`:         [Crucible symbolic execution engine](https://github.com/GaloisInc/crucible)
* `deps/cryptol/`:          [Cryptol](https://github.com/GaloisInc/cryptol)
* `deps/jvm-verifier/`:     [Java Symbolic Simulator (JSS)](https://github.com/GaloisInc/jvm-verifier)
* `deps/saw-core/`:         [SAWCore intermediate language](https://github.com/GaloisInc/saw-core), used by CSS, JSS, and SAWScript

## For SAW developers

Presently, the `saw-script` main executable cannot be loaded into GHCi due to a
linker issue. However, the rest of the library can be manipulated in GHCi, with
a little convincing.

If you are using `cabal` to build, select the `saw-script` target:

```
$ cabal new-repl saw-script
```

If you are using `stack` to build, select the `saw-script` *library* target:

```
$ stack repl saw-script:lib
```

In order to use interactive tools like `intero`, you need to configure them with
this target. You can configure `intero-mode` in Emacs to use the `saw-script`
library target by setting the variable `intero-targets` to the string
`"saw-script:lib"`. To make this setting persistent for all files in this
project, place the following snippet in the file `src/.dir-locals.el`:

```elisp
((haskell-mode
  (intero-targets "saw-script:lib")))
```

## Acknowledgements

Much of the work on SAW has been funded by, and lots of design input was
provided by the team at the [NSA's Laboratory for Advanced Cybersecurity
Research](https://www.nsa.gov/what-we-do/research/cybersecurity-research/),
including Brad Martin, Frank Taylor, and Sean Weaver.

Portions of SAW are also based upon work supported by the Office
of Naval Research under Contract No. N68335-17-C-0452. Any opinions,
findings and conclusions or recommendations expressed in this
material are those of the author(s) and do not necessarily reflect
the views of the Office of Naval Research.
