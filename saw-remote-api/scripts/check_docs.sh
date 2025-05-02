#! /bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

echo "Checking saw-remote-api docs (SAW.rst) are up-to-date with server"

cd $DIR/../../saw-server/docs

export SAW_SERVER=$(which saw-remote-api)
if [[ ! -x "$SAW_SERVER" ]]; then
  echo "could not locate saw-remote-api executable - try executing with cabal v2-exec"
  exit 1
fi

$SAW_SERVER doc > TEMP.rst
diff SAW.rst TEMP.rst
