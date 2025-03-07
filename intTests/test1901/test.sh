set -e

# The bug is not yet fixed, so this is expected to fail.
! $SAW test.saw
