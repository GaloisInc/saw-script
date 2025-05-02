Integration tests for SAWScript
===============================

Running tests
-------------

The integration tests are exposed as the [cabal test suite](../saw.cabal)
`integration_tests`. The default tests can be run with:

```
cabal test --enable-tests integration_tests
```

For each `test_*` directory that is not listed in the `DISABLED_TESTS`
environment variable or the `disabled_tests.txt` if the environment variable
isn't set, invoke the `test.sh` in that directory with some supporting
environment variables set. The `test.sh` should complete with a return code of 0
on no error or non-zero on error.

If the `DISABLED_TESTS` environment variable is set, the `disabled_tests.txt`
file is ignored. Both may specify tests separated by spaces and/or newlines, and
the `#` character starts a comment to the end of the current line.

The `ENABLED_TESTS` environment variable, if set, overrides the set of
discovered tests to include only those in the `ENABLED_TESTS` list. This
environment variable is commonly used during development to run specific tests
(which `cabal test` does not easily support).

You can in most cases run a single test locally with `SAW=path-to-saw
bash test.sh` where `path-to-saw` is the SAW executable to test.
If you don't have your shell configured to report exit status, remember
to check that explicitly afterwards with `echo $?` -- not all the tests
will necessary produce overt errors on failure, especially if something
is wrong and cases that should be failing aren't.

Creating tests
--------------

A test is defined by a directory which contains a shell script called "test.sh";
the test succeeds when the shell script does. When run as part of the suite,
these "test.sh" scripts are interpreted by `bash`.
The convention (not yet broadly enforced) is that these scripts do not have
a `#!` header and are not marked executable; they are run explicitly with
`bash test.sh` by the test infrastructure.
This avoids assorted problems on Windows.

Tests generally consist of a SAW script that is expected to succeed together
with the artefacts that are needed. The test suite defines the environment
variable "SAW", pointing to the corresponding executable, and with appropriate
Java classpaths included. It's a good idea to include a README in each test
directory.

For tests that need binary artefacts (Java bytecode, LLVM bitcode) or
things that might as well be (linked-mir.json from mir-json), include
the corresponding source and a (gmake) Makefile that builds the
artefact, as well as the artefact itself.
Indicate other provenance information in the Makefile (e.g. LLVM version and
host type), and to what extent this is expected to affect the utility of the
artefact for testing.
`test2122` is a good example to crib from.

If the test directory name starts with "test", and the directory name is not
included in the `disabled_tests.txt` file or `DISABLED_TESTS` environment
variable, then the test is run by default. Only default tests are run on the
build slaves. When disabling a test by default, explain why in that test's
README.

For tests related to issues, use the issue number in the directory name,
like `test2122`.
