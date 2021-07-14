#!/bin/bash
git submodule update --init

function install() {
  cp $(find dist-newstyle -type f -name $1 | sort -g | tail -1) bin/
}

cabal build exe:cryptol exe:saw exe:saw-remote-api

rm -rf bin && mkdir bin
install cryptol
install saw
install saw-remote-api

echo
echo "COPIED EXECUTABLES TO `pwd`/bin."
