[![Build Status](https://github.com/GaloisInc/saw-script/workflows/SAWScript/badge.svg)](https://github.com/GaloisInc/saw-script/actions?query=event%3Aschedule)

# SAW

This repository contains the code for SAW, the Software
Analysis Workbench.
SAW provides the ability to reason about
formal models describing the denotation of programs written in
languages such as C, Java, Rust, and Cryptol.

SAWScript is the scripting language that serves as the primary
user interface to SAW.
The repository is named after it for historical reasons.

## Documentation

There are two SAW tutorials that give an introduction to using the
SAWScript interpreter:

* [This tutorial](https://github.com/GaloisInc/saw-script/blob/master/doc/pdfs/llvm-java-verification-with-saw.pdf) gives an
  introduction to verifying C code (using LLVM) and Java code (using JVM).
* [This tutorial](https://github.com/GaloisInc/saw-script/blob/master/doc/pdfs/rust-verification-with-saw.pdf)
  gives an introduction to verifying Rust code (using MIR).

There is also a longer
[manual](https://github.com/GaloisInc/saw-script/blob/master/doc/pdfs/saw-user-manual.pdf)
that describes the breadth of SAW's features.

## Precompiled Binaries

Precompiled SAW binaries for a variety of platforms are available
on the [releases
page](https://github.com/GaloisInc/saw-script/releases).

## Docker Images

Alternatively, there is a Docker image available from the [packages
page](https://github.com/orgs/GaloisInc/packages/container/package/saw).

## Getting Z3

SAW can use many theorem provers, but because of its use of Cryptol it
always needs to have Microsoft Research's [Z3 SMT
solver](https://github.com/Z3Prover/z3) installed.  You can download Z3
binaries for a variety of platforms from their [releases
page](https://github.com/Z3Prover/z3/releases).
You can also download binaries for Z3 and other solvers from our
[what4-solvers](https://github.com/GaloisInc/what4-solvers/releases)
package.

We currently recommend Z3 4.8.10. If you plan to use path satisfiability
checking, you'll also need Yices version 2.6.1 or newer.

After installation, make sure that `z3` (or `z3.exe` on Windows)
is on your PATH.

## Cloning the Repository

After cloning the saw-script repository, you need to also clone
submodules.
Run `git submodule update --init`.
The commonly used `--recursive` option is not required, and also not
recommended as it results in cloning a considerable number of
additional unused subtrees.

## Downloading Release Sources

Starting with SAW 1.4, to download the sources for a release from the
[releases page](https://github.com/GaloisInc/saw-script/releases),
be sure to get the file `saw-<release>-sources.tar.gz` and not the
default GitHub-generated file `v<release>.tar.gz`.
The latter does not include SAW's submodules and is, alas, therefore
unbuildable.
(This is
[a GitHub problem](https://github.com/orgs/community/discussions/6003)
and there's no sign of it being likely to get fixed.)

For releases prior to 1.4, the best way to get a buildable version of
the release source is to clone the repository and check out the
release tag (e.g. `v1.3`).

## Manual Installation

To build SAW and related utilities from source:

  * Ensure that you have the C libraries and header files for
    `terminfo`, which generally comes as part of `ncurses` on most
    platforms. On Fedora, it is part of the `ncurses-compat-libs` package.
    You will also need the C headers and libraries for `zlib`.
    Some platforms split library packages into runtime and development
    portions; you need the development packages.

  * Ensure that you have the `cabal` and `ghc` executables in your
    `PATH`. If you don't already have them, we recommend using `ghcup`
    to install them: <https://www.haskell.org/ghcup/>. We recommend
    Cabal 3.10 or newer, and GHC 9.4, 9.6, or 9.8.
    You may need to install additional system packages for this as well,
    most likely `gmp` and `perl`.

  * Ensure that you have Z3 installed (as described above) and that
    the `z3` binary is on your `PATH`.

  * Optionally, put in place dependency version freeze files:

        ln -s cabal.<ghc version>.config cabal.project.freeze

  * Run `cabal update` if you had installed `cabal` prior to using this README.

  * Build SAW by running

        ./build.sh

    The SAW executables will be available in the `bin` directory.

    Note that running `cabal build` or `cabal install` directly will not work.

  * Optionally, run ./stage.sh to create a binary tarball.

## Notes on LLVM

SAW can analyze LLVM programs (usually derived from C, but potentially
for other languages). The only tool strictly required for this is a
compiler that can generate LLVM bitcode, such as `clang`. However,
having the full LLVM tool suite available can be useful. We have tested
SAW with LLVM and `clang` versions from 3.5 to 20.0, as well as the
version of `clang` bundled with Apple Xcode. We welcome bug reports on
any failure to parse bitcode from LLVM versions in that range.

Note that successful parsing doesn't necessarily mean that verification
will be possible for all language constructs. There are various
instructions that are not supported during verification. However,
any failure during `llvm_load_module` should be considered a bug.

## Notes on Java

To work with Java programs, you will need a JDK installed.
Make sure the `javac` binary is on your `PATH`.

## Notes on Rust

SAW also has support for analyzing Rust programs, based on the MIR intermediate
representation.
For this purpose, one must compile Rust code using
[`mir-json`](https://github.com/GaloisInc/mir-json), a tool which
compiles Rust code to a machine-readable, JSON-based format.
A copy of `mir-json` is bundled with SAW as a git submodule.
For best results, always use that version of `mir-json`.

Sometimes as `mir-json` evolves, its output format changes.
These changes are captured in a _schema version_; SAW and `mir-json` must
agree on the schema version.
(So far, backwards compatibility with old schema versions has proven
impractical.)
If after updating SAW, preexisting JSON output files no longer load because
of a schema version mismatch, recompile them with the corresponding updated
version of `mir-json`.

`mir-json` is a Rust compiler plugin and works with a specific version of
the Rust compiler.
Instructions for installing the proper Rust compiler, building and installing
`mir-json` itself, and then using it to compile the Rust standard libraries
can be found
[in the `mir-json` repository](https://github.com/GaloisInc/mir-json#installation-instructions).

The installation instructions will tell you to set the `SAW_RUST_LIBRARY_PATH`
environment variable to point at the compiled standard libraries.
SAW uses this environment variable to find them; it must be set to use the
Rust verification subsystem.

Currently, SAW supports [version
9](https://github.com/GaloisInc/mir-json/blob/master/SCHEMA_CHANGELOG.md#9) of
`mir-json`'s schema.

## Notes on Windows

If you have trouble loading the SAW REPL on Windows, try invoking it
with the `--no-color` option.

## Related Packages

Many dependencies are automatically downloaded into `deps/` when you
build using `build.sh`; see
[Manual Installation](#manual-installation) above. Key automatically
downloaded dependencies include:

* `deps/crucible/`:         [Crucible symbolic execution engine](https://github.com/GaloisInc/crucible)
* `deps/cryptol/`:          [Cryptol](https://github.com/GaloisInc/cryptol)

## Notes on Freeze Files

We use the `cabal.GHC-*.config` files to constrain dependency versions
in CI, and recommend using the following command for best results before
building locally:

```
ln -s cabal.GHC-<VER>.config cabal.project.freeze
```

These configuration files were generated using `cabal freeze`, but with
some manual changes to allow cross-platform builds, since Unix-like
systems and Windows systems end up with different package dependencies.
Specifically, we remove lines for the following packages or flags:

```
cryptol-saw-core
regex-posix
saw-remote-api
saw-script
tasty +unix
unix
unix-compat
unix-time
zlib -bundled-c-zlib +non-blocking-ffi +pkg-config
```

## Acknowledgements

Much of the work on SAW has been funded by, and lots of design input was
provided by the team at the [NSA's Laboratory for Advanced Cybersecurity
Research](https://www.nsa.gov/Research/NSA-Mission-Oriented-Research/LAC/),
including Brad Martin, Frank Taylor, and Sean Weaver.

Portions of SAW are also based upon work supported by the Office
of Naval Research under Contract No. N68335-17-C-0452. Any opinions,
findings and conclusions or recommendations expressed in this
material are those of the author(s) and do not necessarily reflect
the views of the Office of Naval Research.
