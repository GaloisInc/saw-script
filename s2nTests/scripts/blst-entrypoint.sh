#!/usr/bin/env bash
set -xe

cd /workdir
./scripts/install.sh
cp /saw-bin/saw bin/saw

wget --quiet -O solvers.zip "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20220902/ubuntu-22.04-bin.zip"
(cd bin && unzip -o ../solvers.zip)
chmod +x bin/*

export PATH=/workdir/bin:$PATH
export CRYPTOLPATH=/workdir/cryptol-specs:/workdir/spec

abc -h || true
z3 --version
yices --version
yices-smt2 --version

./scripts/build_x86.sh
./scripts/build_llvm.sh

saw proof/memory_safety.saw

./scripts/check.sh | if grep False; then exit 1; fi
