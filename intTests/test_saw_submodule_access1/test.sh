set -e
  # all must pass.

$SAW test_import_errors.saw

$SAW test_import_D.saw

! $SAW test_load_D.saw

  # finishing https://github.com/GaloisInc/saw-script/pull/2593
  #  should allow test_load_D.saw to succeed. (as it should)
  # TODO: remove the ! above when that PR is done.

$SAW test_UseFunctors.saw
