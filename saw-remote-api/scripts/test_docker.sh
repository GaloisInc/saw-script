#!/bin/bash

echo "Testing saw-remote-api docker image..."

cleanup () {
  echo "killing saw-remote-api docker container"
  docker container kill saw-remote-api || true
  docker container rm saw-remote-api || true
}
trap cleanup EXIT

DIR="$( dirname "$( dirname "${BASH_SOURCE[0]}" )")"

TAG=${1:-saw-remote-api}

( cd "$DIR";
  docker run --name=saw-remote-api -d \
    --env CLASSPATH=/home/saw/tests/saw/test-files \
    -v $PWD/../saw-python/tests/saw/test-files:/home/saw/tests/saw/test-files \
    -p 8080:8080 \
    "$TAG";

  if (( $? != 0 )); then
    echo "Failed to launch docker container"
    exit 1
  fi
)

sleep 5 # let the server catch its breath and be ready for requests

( cd "$DIR/../saw-python";

  NUM_FAILS=0;
  function run_test {
    "$@"
    if (( $? != 0 )); then NUM_FAILS=$(($NUM_FAILS+1)); fi
  };


  echo "Setting up python environment for remote server clients...";
  poetry install;

  export SAW_SERVER_URL="http://localhost:8080/";
  run_test poetry run python -m unittest discover tests/saw;
  run_test poetry run python -m unittest discover tests/saw_low_level;

  if [ $NUM_FAILS -eq 0 ]
  then
    echo "All docker saw-remote-api tests passed"
    exit 0
  else
    echo "Some docker saw-remote-api tests failed"
    exit 1
  fi
)
