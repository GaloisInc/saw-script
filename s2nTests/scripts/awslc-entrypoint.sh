#!/usr/bin/env bash
set -xe

cd /saw-script/aws-lc-verification/SAW
./scripts/install.sh
cp /saw-bin/saw bin/saw

export PATH=/saw-script/aws-lc-verification/SAW/bin:$PATH
export CRYPTOLPATH=/saw-script/aws-lc-verification/cryptol-specs

./scripts/build_x86.sh
./scripts/build_llvm.sh
./scripts/post_build.sh
./scripts/quickcheck.sh
