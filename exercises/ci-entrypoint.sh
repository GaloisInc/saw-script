#!/usr/bin/env bash
set -xe

# This script checks all of the exercise and solution files.  It is only
# intended to be executed by the saw-script CI system.

cd /workdir
mkdir bin
cp /saw-bin/saw bin/saw
cp /saw-bin/abc bin/abc
cp /saw-bin/yices bin/yices
cp /saw-bin/yices-smt2 bin/yices-smt2
cp /saw-bin/z3 bin/z3
chmod +x bin/*

export PATH=/workdir/bin:$PATH

abc -h || true
z3 --version
yices --version
yices-smt2 --version

# Run SAW over all exercises and solutions
find . -name solution.saw -o -name exercise.saw | xargs -I % sh -c "saw % || exit 255"
