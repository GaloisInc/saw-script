set -e

$SAW test.saw

# These tests should fail
! $SAW test-fail.saw
