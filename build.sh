#!/bin/bash
git submodule update --init
(cd deps/abcBridge && git submodule update --init)

function install() {
  cp $(find dist-newstyle -type f -name $1 | sort -g | tail -1) bin/
}

cabal build exe:cryptol exe:jss exe:saw exe:saw-remote-api

rm -rf bin && mkdir bin
install cryptol
install jss
install saw
install saw-remote-api

echo
echo "COPIED EXECUTABLES TO `pwd`/bin."
