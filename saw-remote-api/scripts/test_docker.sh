#!/bin/bash

echo "Building and testing saw-remote-api docker image..."

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

TAG=${1:-saw-remote-api}

pushd $DIR/../..

docker build -t saw-remote-api --file saw-remote-api/Dockerfile .
popd

pushd $DIR/..

docker run --name=saw-remote-api -d \
  -v $PWD/python/tests/saw/test-files:/home/saw/tests/saw/test-files \
  -p 8080:8080 \
  "$TAG"

if (( $? != 0 )); then
  echo "Failed to launch docker container"
  exit 1
fi

popd

sleep 5 # let the server catch its breath and be ready for requests

pushd $DIR/../python

NUM_FAILS=0
function run_test {
    "$@"
    if (( $? != 0 )); then NUM_FAILS=$(($NUM_FAILS+1)); fi
}


echo "Setting up python environment for remote server clients..."
poetry install

export SAW_SERVER_URL="http://localhost:8080/"
run_test poetry run python -m unittest discover tests/saw
run_test poetry run python -m unittest discover tests/saw_low_level

popd

echo "killing saw-remote-api docker container"

docker container kill saw-remote-api


if [ $NUM_FAILS -eq 0 ]
then
  echo "All docker saw-remote-api tests passed"
  exit 0
else
  echo "Some docker saw-remote-api tests failed"
  exit 1
fi
