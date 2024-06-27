#!/bin/sh
# build.sh: build SAW
# usage: ./build.sh
set -e

git submodule update --init

function install() {
  # XXX: this should probably sort by timestamp (to get the file just
  # built) rather than version. (Also, -g will not necessarily process
  # versions correctly, since it's intended for floats, and it may not
  # be as portable as we'd like.)
  cp $(find dist-newstyle -type f -name $1 -print | sort -g | tail -1) bin/
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
