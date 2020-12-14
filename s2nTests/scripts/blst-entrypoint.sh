#!/usr/bin/env bash
set -xe

cd /saw-script/blst-verification
./scripts/install.sh
cp /saw-bin/saw bin/saw

export PATH=/saw-script/blst-verification/bin:$PATH
export CRYPTOLPATH=/saw-script/blst-verification/cryptol-specs:/saw-script/blst-verification/spec

./scripts/build_x86.sh

# TODO: replace this section with ./scripts/build_llvm.sh once the absolute
# path in that script is removed.
(
    mkdir -p build/llvm
    rm -r build/llvm
    cp -r blst build/llvm
    cd /saw-script/blst-verification/build/llvm
    for p in /saw-script/blst-verification/patches/*
    do
        patch -p1 -t < "$p"
    done
    export CFLAGS='-g -fPIC -Wall -Wextra -Werror'
    export CC=wllvm
    export LLVM_COMPILER=clang
    ./build.sh
    extract-bc --bitcode libblst.a
)

./scripts/prove.sh
./scripts/check.sh | if grep False; then exit 1; fi
