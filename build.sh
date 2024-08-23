#!/bin/sh
# build.sh: build SAW
# usage: ./build.sh
set -e

git submodule update --init

install() {
  PROG=$(cabal list-bin exe:$1)
  cp $PROG bin/
}

cabal build exe:cryptol exe:saw exe:saw-remote-api \
            exe:crux-mir-comp exe:extcore-info exe:verif-viewer

rm -rf bin && mkdir bin
install cryptol
install saw
install saw-remote-api
install crux-mir-comp
install extcore-info
install verif-viewer

echo
echo "COPIED EXECUTABLES TO `pwd`/bin."
