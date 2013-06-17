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
cabal-dev install --force-reinstalls ../Verinf
cabal-dev install --force-reinstalls ../SAWCore
cabal-dev install --force-reinstalls ../Java --constraint="statistics==0.10.3.1"
cabal-dev install --force-reinstalls ../LLVM
cabal-dev install --force-reinstalls
