#!/usr/bin/env bash

if ! [ -f /saw-script/bin/saw ]; then
  echo "error: /saw-script/bin/saw does not exist. Was this container ran with the correct volume mount?" >&2
  exit 1
fi

if [ $# -eq 0 ]; then # no arguments passed
  TESTS=sawHMAC
  source codebuild/bin/s2n_setup_env.sh
  exec bash
else
  TESTS="$1"
  shift
  source codebuild/bin/s2n_setup_env.sh
  exec codebuild/bin/s2n_codebuild.sh "$@"
fi
