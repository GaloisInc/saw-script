#!/usr/bin/env bash
set -xe

cd /workdir
mkdir bin
cp /saw-bin/saw bin/saw

wget --quiet -O solvers.zip "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20220902/ubuntu-22.04-bin.zip"
(cd bin && unzip -o ../solvers.zip)
chmod +x bin/*

export PATH=/workdir/bin:$PATH

abc -h || true
z3 --version
yices --version
yices-smt2 --version

# TODO: Add all tests
saw sha512/exercise.saw
saw sha512/solution.saw
