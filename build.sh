#!/bin/sh
set -e

cabal-dev install --force-reinstalls ../../abcBridge
cabal-dev install --force-reinstalls ../../jvm-parser
cabal-dev install --force-reinstalls ../../llvm-pretty
cabal-dev install --force-reinstalls ../Verinf
cabal-dev install --force-reinstalls ../SAWCore
cabal-dev install --force-reinstalls ../Java --constraint="statistics==0.10.3.1"
cabal-dev install --force-reinstalls ../LLVM
cabal-dev install --force-reinstalls
