#!/usr/bin/env bash
set -xe

cd /workdir
./scripts/install.sh
cp /saw-bin/saw bin/saw

export PATH=/workdir/bin:$PATH
export CRYPTOLPATH=/workdir/cryptol-specs:/workdir/spec

./scripts/build_x86.sh
./scripts/build_llvm.sh

./scripts/prove.sh
./scripts/check.sh | if grep False; then exit 1; fi
