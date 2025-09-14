set -e
  # all must pass.

$SAW test_import_errors.saw

$SAW test_import_D.saw

# $SAW test_load_D.saw
#   - This is a test that will fail till till code is fixed.
#   - TODO: uncomment after fixing code.

$SAW test_UseFunctors.saw
