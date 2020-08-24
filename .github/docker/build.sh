#!/usr/bin/env bash
set -euo pipefail

CURRENT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" > /dev/null 2>&1 && pwd)"
cd "$CURRENT_DIR/../.." # saw-script root folder

cmd="$1"
shift

case "$cmd" in
  s2n)
    TESTS="${1:-bash}"
    shift
    docker build -t s2n --file .github/docker/s2n.dockerfile .
    docker run -d --name s2n -it -v "$PWD":/saw-script s2n "$TESTS" "$@"
    exit
    ;;
  saw-script)
    docker build -t saw-script -- file .github/docker/saw-script.dockerfile .
    docker run -d --name saw-script -it -v "$PWD":/saw-script saw-script
    docker exec saw-script cabal update
    docker exec saw-script cabal build all
    docker exec saw-script bash -c 'cp $(cabal exec which saw) bin'
    docker exec saw-script bash -c 'cp $(cabal exec which jss) bin'
    exit
    ;;
esac
