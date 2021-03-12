#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

pushd $DIR/../python

NUM_FAILS=0
function run_test {
    "$@"
    if (( $? != 0 )); then NUM_FAILS=$(($NUM_FAILS+1)); fi
}

echo "Setting up python environment for remote server clients..."
poetry install

# Ask cabal where the server is, and if that does work... check
# the places CI will place the executable as a backup
export SAW_SERVER=$(cabal v2-exec which saw-remote-api)
if [[ -x "$SAW_SERVER" ]]; then
  echo "using saw-remote-api at $SAW_SERVER"
elif [[ -x "$DIR/../../dist/bin/saw-remote-api" ]]; then
  export SAW_SERVER="$DIR/../../dist/bin/saw-remote-api"
  echo "using saw-remote-api at $SAW_SERVER"
elif [[ -x "$DIR/../../dist/bin/saw-remote-api.exe" ]]; then
  export SAW_SERVER="$DIR/../../dist/bin/saw-remote-api.exe"
  echo "using saw-remote-api at $SAW_SERVER"
else
  echo "could not locate saw-remote-api executable"
  exit 1
fi

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
