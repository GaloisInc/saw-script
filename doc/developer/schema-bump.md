# Bumping the mir-json schema version

Because we don't attempt to provide backward compatibility for
mir-json schema versions, it's important to keep close track of what
schema version is supported, and also to regenerate any and all
mir-json blobs after a schema version change.

## Updating the current schema version

The current schema version appears in two places: at the top of
`CHANGES.md` and near the bottom of `README.md` in the "Notes on Rust"
section.
Update both.

There is no need to add a separate entry to `CHANGES.md` saying you
bumped the schema version.

## Updating the mir-json blobs

There are three sets of mir-json blobs in the tree:
- in the integration tests (`intTests`)
- in the Python tests
- in the Rust tutorial

Be sure that the mir-json version that gets run when you go to update
these is the new one with the new schema version.
Also make sure that the mir-json submodule in the SAW tree points at
the right version of mir-json; its commit hash will be recorded for
reference.

### Updating the integration tests

Most of the work is automated; go to the `intTests` subdirectory and
run `make regen-mir-blobs`.
This will rebuild all the `*.linked-mir.json` files and update the
`*.FROM` files that record the mir-json version and other info.

One test intentionally contains disambiguators in identifiers:
- `test_mir_verify_basic/test.saw` contains (near the bottom) a
  disambiguated name in order to make sure that references to
  disambiguated names continue to work.
  This will need to be updated after regenerating the blob.
  You can check that it works without engaging all the test suite
  apparatus by just running `saw test.saw` in that directory;
  this should take less than two seconds to run.

There are several more tests that contain disambiguators in
identifiers in checked output.
(This is a bug. See #2614.)
You can find these with (from `intTests/`):
```
grep -l 'Verifying.*::' */*.good
```

To update the output, in each directory that contains one of these
outputs, first run
```
SAW=saw sh ./test.sh
```

which will then print diffs showing that the disambiguators have
changed (if there are more diffs that show other things, investigate
before proceeding), then to accept those changes,
```
SAW=saw sh ./test.sh good
```

and then commit all the updated reference files along with the rest of
the changes.

### Updating the Python tests

The procedure for the Python tests is the same, except that the place
to run `make regen-mir-blobs` is `saw-python/tests/saw/test-files`.

None of these are expected to contain disambiguators that need
updating.

### Updating the tutorial files

To update these, go to the directory `doc/rust-verification-with-saw/code`
and run first `make clean` then `make`.
