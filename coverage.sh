#!/bin/bash

cabal build --enable-coverage exe:saw

# This conflicts with GitRev.mix in `saw-script`. Yuck.
rm -f ./dist-newstyle/build/*/ghc-*/cryptol-*/**/GitRev.mix

(cd intTests && CABAL_FLAGS="--enable-coverage" ./runtests.sh)

hpc sum --output=saw.tix --union --exclude=Main $(find intTests -name saw.tix)

HPC_ARGS="--destdir=coverage"

# Collect up all the directories where `.mix` files might live. This is
# horrendous.
HPC_DIRS=$(find dist-newstyle -name "*.mix" | xargs -n 1 dirname | sort -u | grep -v dyn)
HPC_DIRS2=$(find dist-newstyle -name "*.mix" | xargs -n 1 dirname | xargs -n 1 dirname | sort -u | grep -v dyn)
for dir in ${HPC_DIRS}; do
    HPC_ARGS="${HPC_ARGS} --hpcdir=${dir}"
done
for dir in ${HPC_DIRS2}; do
    HPC_ARGS="${HPC_ARGS} --hpcdir=${dir}"
done

# Add the top-level directory of each dependency package to the source
# file search path.
HPC_ARGS="${HPC_ARGS} --srcdir=."
for dir in $(cat cabal.project | grep -v : | grep -v "\.cabal") ; do
    HPC_ARGS="${HPC_ARGS} --srcdir=${dir}"
done

hpc markup ${HPC_ARGS} saw.tix
