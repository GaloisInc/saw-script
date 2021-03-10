#! /bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

echo "Checking saw-remote-api docs (SAW.rst) are up-to-date with server"

cd $DIR/../docs

export SAW_SERVER=$(cabal v2-exec which saw-remote-api)
if [[ -x "$SAW_SERVER" ]]; then
  echo "using saw-remote-api at $SAW_SERVER"
else
  echo "cabal could not locate saw-remote-api via the which command"
  exit 1
fi

$SAW_SERVER doc > TEMP.rst
diff SAW.rst TEMP.rst
