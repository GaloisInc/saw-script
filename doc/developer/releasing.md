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
   - successful tests on all test suites,
   - an up-to-date [`SOURCE_DATE_EPOCH`](../scripts/epoch.mk) for documentation builds,
   - up-to-date [documentation PDFs](../pdfs), and
   - an up-to-date [CHANGES.md](../../CHANGES.md) file.

2. Create a draft release on GitHub
3. Make a commit on the `release-n.n` branch updating the version in the
   `saw.cabal` file to `n.n`. This will trigger a build.
4. Once the build is done, download the release artifacts from the
   outputs of the build. These are `.zip` files containing `.tar.gz` and
   `.sig` files.
5. Unpack the `.zip` files and attach the `.tar.gz` and `.sig` files to
   the draft release.
6. Publish the release. This will add a tag to the release branch, as
   well.
7. Announce the release and update release-relevant information in the following places:

   - <saw@galois.com>
   - <saw-users@galois.com>
   - @galois on Twitter (for major releases)
