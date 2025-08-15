export SAW_TEST_ENV=fnord
exec ${TEST_SHELL:-bash} ../support/test-and-diff.sh "$@"
