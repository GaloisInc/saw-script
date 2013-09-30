#!/bin/sh
set -e

REPOS="abcBridge jvm-parser llvm-pretty"

if [ ! -e ./build ] ; then
  mkdir build
fi

for repo in ${REPOS} ; do
  if [ ! -e ./build/${repo} ] ; then
    git clone src.galois.com:/srv/git/${repo}.git ./build/${repo}
  fi
done

cabal-dev install --force-reinstalls ./build/abcBridge
cabal-dev install --force-reinstalls ./build/jvm-parser
cabal-dev install --force-reinstalls ./build/llvm-pretty
cabal-dev install --force-reinstalls ../Verinf --enable-tests
cabal-dev install --force-reinstalls ../SAWCore --enable-tests
cabal-dev install --force-reinstalls ../Java --enable-tests
cabal-dev install --force-reinstalls ../LLVM --enable-tests
cabal-dev install --force-reinstalls --enable-tests
