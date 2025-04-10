set -e

#####
## See the README for an explanation of what each of these files test.
#####

# These tests should pass
$SAW test-appropriate-overrides.saw
$SAW test-global-initializer.saw
$SAW test-sketchy-overrides-O2.saw
$SAW test-signed.saw

# These tests should fail
! $SAW test-no-init.saw
! $SAW test-sketchy-overrides-O1.saw
! $SAW test-signed-fail.saw
