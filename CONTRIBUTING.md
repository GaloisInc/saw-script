# SAW development

This document explains our standards for developing SAW. Our goals are
to have a development process that:

- consistently yields reliable software artifacts,
- quickly incorporates improvements and gets them into user hands, and
- allows new contributors to have an immediate impact.

It describes our methods and practices for:

- testing and continuous integration;
- organizing, branching, and merging this repository;
- producing and publishing release artifacts; and
- feature and release planning.

This is a living document that is not (and possibly cannot be)
comprehensive. If something is missing or unclear, or if you have
suggestions for improving our processes, please file an issue or open a
pull request.

# Building

See guidance in [README.md](README.md) for information on building SAW.

# Testing

The core test suite for SAW consists of a collection of integration
tests, in subdirectories of the `intTest` directory. A Cabal test suite
called `integration_tests` is responsible for invoking these tests.

## Dependency freezing

To ensure repeatable test results, our CI system uses
`cabal.project.freeze` files to fix the version of all dependencies
prior to building. It uses one of several version freezing files, each
named `cabal.GHC-<VER>.config`, for GHC version `<VER>`.

We recommend building and testing using these files unless your explicit
goal is to assess compatibility with different library versions. To do
so, run the following before building or testing:

    ln -s `cabal.GHC-<VER>.config cabal.project.freeze

## Running and Creating Tests

For more information on running and creating tests, see the [README.md
file in the intTests directory](intTests/README.md).

## Other Tests in CI

Although individual developers typically run just the core integration
tests, our CI system (GitHub Actions) runs several other tests on every
pull request. These include ensuring that a variety of large proof
developments, many for the [s2n TLS
library](https://github.com/aws/s2n-tls), continue to succeed. The
scripts for running these tests are located in the [s2nTests](s2nTests)
directory.

# Repository organization and practices

The top-level repository directories are:

* `src` - Source code for the SAWScript interpreter library.

* `saw` - Source for the `saw` executable interpreter for SAWScript.

* `doc` - A tutorial and manual for SAWScript.

* `examples` - Various examples of using SAWScript.

* `intTests` - The central test suite for SAWScript.

* `s2nTests` - Additional tests for SAWScript, confirming that
  verifications involving the s2n library continue to work.

* `saw-remote-api` - Source for a server that provides a remote API to
  SAW based on JSON-RPC, and a Python client for that API.

* `saw-core` - Source code for the SAWCore intermediate language used
  within SAW.

* `saw-core-aig` - A library for translating SAWCore to And-Inverter
  Graphs.

* `saw-core-coq` - A library for translating SAWCore to Coq's Gallina
  language.

* `saw-core-sbv` - A library for translating SAWCore predicates to SMT
  queries using the [SBV](http://leventerkok.github.io/sbv/) library.

* `saw-core-what4` - A library for translating SAWCore predicates to
  solver queries using the [What4](https://github.com/galoisinc/what4)
  library.

* `cryptol-saw-core` - A library for translating
  [Cryptol](https://cryptol.net) code into SAWCore.

* `rme` - A library implementing a Reed-Muller Expansion datatype for
  representing Boolean formulas.

* `deps` - A location for other dependencies included as Git submodules.

* `crux-mir-comp` - A version of [Crux](https://crux.galois.com/) that
  can perform modular analysis of Rust code using a form of contracts.

## Branching and merging

Within the `GaloisInc/saw-script` repository, we use a variation on the
[git-flow
model](http://nvie.com/posts/a-successful-git-branching-model/) for
branches and merging with they key difference that our `master` (rather
than `develop`) branch serves as the cutting edge development branch,
and our `release-*` (rather than `master`) branches are where only
pristine, tagged releases are committed.

In short:

- All changes should be developed on branches and then merged into
  `master` when completed.

- When we reach a feature freeze for a release, we create a new branch
  prefixed with `release-`, for example `release-0.3`. When the release
  is made, we merge those changes back into `master` and tag the `HEAD`
  of the `release` branch.

- If a critical bug emerges in already-released software, we create a
  branch off of the relevant `release` branch. When the hotfix is
  complete, we merge those changes back into `master` and add a tag on
  the `release` branch.

- Merging PRs requires a review from at least one other committer, and
  requires successful completion of a CI workflow including a wide
  variety of tests. Branches must be up-to-date with `master` before
  merging.
  
## Using Mergify

Due to the requirement that PRs pass CI and code review and are
up-to-date with `master` before merging, it can be time-consuming to
manually manage a large queue of changes to be merged. To help reduce
this burden we use the [Mergify](https://mergify.io/) tool. It
automatically queues up CI runs and merges PRs once CI and code review
have succeeded. To indicate that a PR is ready for Mergify to merge, add
the `ready-to-merge` label.

# Releases

We take the stability and reliability of our releases very seriously. To
that end, our release process is based on principles of _automation_,
_reproducibility_, and _assurance_.

Automation is essential for reducing the possibility of human error. The
checklist for a successful release is fairly lengthy, and most of the
steps need not be done by hand. The real points of judgment for an
individual release are deciding _when_ the codebase is ready to be
released, not _how_ it is released.

Reproducibility is essential for fixing bugs both in hotfixes and future
mainline development. If we cannot reproduce the circumstances of a
release, we might not be able to reproduce bugs that are reported by
users of that release. Bugs are often very particular about the
environment where they will arise, so it is critical to make the
environment of a release consistent.

## Creating releases

The release process is:

1. Make sure the `release-n.n` branch is in a release/ready state, including:
   - successful build artifacts across all platforms,
   - successful tests on all test suites, and
   - an up-to-date [CHANGES.md](CHANGES.md) file.
1. Create a draft release on GitHub
1. Make a commit on the `release-n.n` branch updating the version in the
   `saw-script.cabal` file to `n.n`. This will trigger a build.
1. Once the build is done, download the release artifacts from the
   outputs of the build. These are `.zip` files containing `.tar.gz` and
   `.sig` files.
1. Unpack the `.zip` files and attach the `.tar.gz` and `.sig` files to
   the draft release.
1. Publish the release. This will add a tag to the release branch, as
   well.
1. Announce the release and update release-relevant information in the following places:

    - <http://saw.galois.com>
    - <saw@galois.com>
    - <saw-users@galois.com>
    - @galois on Twitter (for major releases)

# Copyright and License

Copyright 2011-2021 [Galois, Inc.](https://galois.com)

Licensed under the BSD 3-Clause License; you may not use this work
except in compliance with the License. A copy of the License is included
in the [LICENSE](LICENSE) file.

# Code of Conduct

This project adheres to the [Contributor Covenant code of
conduct](CODE_OF_CONDUCT.md). By participating, you are expected to
uphold this code. Please report unacceptable behavior to
[saw@galois.com](mailto:saw@galois.com).
