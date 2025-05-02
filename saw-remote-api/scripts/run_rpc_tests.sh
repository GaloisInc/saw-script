#!/bin/bash

set -euo pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

pushd $DIR/../../saw-python

NUM_FAILS=0
function run_test {
    "$@"
    if (( $? != 0 )); then NUM_FAILS=$(($NUM_FAILS+1)); fi
}

echo "Setting up python environment for remote server clients..."
poetry install

echo "Typechecking code with mypy..."
# Don't run mypy on tests/ yet, as it doesn't play well with mypy. See #1125.
run_test poetry run mypy --install-types --non-interactive saw_client/ || true
run_test poetry run mypy --install-types --non-interactive saw_client/

export SAW_SERVER=$(which saw-remote-api)
if [[ ! -x "$SAW_SERVER" ]]; then
  export SAW_SERVER=$(cabal v2-exec which saw-remote-api)
  if [[ ! -x "$SAW_SERVER" ]]; then
    echo "could not locate saw-remote-api executable"
    exit 1
  fi
fi

export CLASSPATH=$(pwd)/tests/saw/test-files

echo "Running saw-remote-api tests..."
echo "Using server $SAW_SERVER"
run_test poetry run python -m unittest discover tests/saw
run_test poetry run python -m unittest discover tests/saw_low_level


popd

if [ $NUM_FAILS -eq 0 ]
then
  echo "All saw-remote-api tests passed"
  exit 0
else
  echo "Some saw-remote-api tests failed"
  exit 1
fi
