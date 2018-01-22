[![Build
Status](https://travis-ci.org/GaloisInc/saw-script.svg?branch=master)](https://travis-ci.org/GaloisInc/saw-script)

# SAWScript

This repository contains the code for SAWScript, the scripting
language that forms the primary user interface to the Software
Analysis Workbench (SAW). It provides the ability to reason about
formal models describing the denotation of programs written in
languages such as C, Java, and Cryptol.

## Documentation

The [SAWScript tutorial](https://saw.galois.com/tutorial.html) gives
an introduction to using the SAWScript interpreter.

## Precompiled Binaries

Precompiled SAWScript binaries for a variety of platforms are available on the [releases page](https://github.com/GaloisInc/saw-script/releases).

## Getting Z3

SAW can use many theorem provers, but because of its use of Cryptol it
always needs to have Microsoft Research's [Z3 SMT
solver](https://github.com/Z3Prover/z3) installed.  You can download Z3
binaries for a variety of platforms from their [releases
page](https://github.com/Z3Prover/z3/releases).

SAW generally requires the most recent version of Z3, which at the
time of writing this file is 4.5.0.

After installation, make sure that `z3` (or `z3.exe` on Windows)
is on your PATH.

## Manual Installation

To build SAWScript and related utilities (CSS, LSS, JSS) from source:

  * Ensure that you have the
    [Stack](https://github.com/commercialhaskell/stack) program on your
    `PATH`. If you don't already have Stack, then `cabal install stack`,
    or download a precompiled binary from
    https://github.com/commercialhaskell/stack/releases.

  * Ensure that you have the C libraries and header files for
    `terminfo`, which generally comes as part of `ncurses` on most
    platforms. On Fedora, it is part of the `ncurses-compat-libs` package.

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
SAW with LLVM and `clang` versions from 3.5 to 4.0, as well as the
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

* `deps/cryptol-verifier/`: [Cryptol Symbolic Simulator (CSS)](https://github.com/GaloisInc/cryptol-verifier)
* `deps/jvm-verifier/`:     [Java Symbolic Simulator (JSS)](https://github.com/GaloisInc/jvm-verifier)
* `deps/llvm-verifier/`:    [LLVM Symbolic Simulator (LSS)](https://github.com/GaloisInc/llvm-verifier)
* `deps/saw-core/`:         [SAWCore intermediate language](https://github.com/GaloisInc/saw-core), used by CSS, JSS, LSS and SAWScript
* `deps/cryptol/`:          [Cryptol](https://github.com/GaloisInc/cryptol)
* `deps/abcBridge/`:        [Haskell bindings for ABC](https://github.com/GaloisInc/abcBridge)

## Acknowledgements

Much of the work on SAW has been funded by, and lots of design input was
provided by the team at the [NSA's Trusted Systems Research
Group](http://www.nsa.gov/research/ia_research/), including Brad Martin,
Frank Taylor and Sean Weaver.

Portions of SAW are also based upon work supported by the Office
of Naval Research under Contract No. N68335-17-C-0452. Any opinions,
findings and conclusions or recommendations expressed in this
material are those of the author(s) and do not necessarily reflect
the views of the Office of Naval Research.
