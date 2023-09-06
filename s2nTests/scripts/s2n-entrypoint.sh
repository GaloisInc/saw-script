#!/usr/bin/env bash
set -xe

export TESTS=$1
if [ "$2" ]; then
    export S2N_LIBCRYPTO=$2
fi

cd /saw-script/s2n
echo 'JOBS=1' >> codebuild/bin/jobs.sh
source codebuild/bin/s2n_setup_env.sh
SAW=true SAW_INSTALL_DIR=tmp-saw ./codebuild/bin/install_default_dependencies.sh
cp /saw-bin/saw "$SAW_INSTALL_DIR"/bin/saw
cp /saw-bin/abc "$SAW_INSTALL_DIR"/bin/abc
"$SAW_INSTALL_DIR"/bin/saw --version
export CFLAGS=-Wno-error=array-parameter
export CLANG=clang
export LLVMLINK=llvm-link
export SAW_SOLVER_CACHE_PATH=/saw-cache
exec codebuild/bin/s2n_codebuild.sh

chmod -R +rw cache
