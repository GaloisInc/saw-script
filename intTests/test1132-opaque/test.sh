# A variant of test1132 that instead uses opaque pointers to ensure that the
# basics of SAW work in an opaque pointer context.
set -e

$SAW test.saw
