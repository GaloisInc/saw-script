#!/bin/bash

# Download or update the dependencies.

set -x
set -v
set -e

if [ ! -e ./deps ] ; then
  mkdir deps
fi

if [ "${OS}" == "Windows_NT" ] ; then
    HERE=$(cygpath -w $(pwd))
else
    HERE=$(pwd)
fi

git submodule init
git submodule update

# Download GHC if necessary.
stack setup

# Remind what version of GHC we're using and where our binaries are
# going.
stack path
