set -e
  # all must pass.

$SAW test_import_errors.saw

$SAW test_import_D.saw

$SAW test_load_D.saw

$SAW test_UseFunctors.saw
