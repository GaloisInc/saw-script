#!/usr/bin/env bash
set -xe

export TESTS=$1
if [ "$2" ]; then
    export S2N_LIBCRYPTO=$2
fi

cd /saw-script/s2n
echo 'JOBS=1' >> codebuild/bin/jobs.sh
source codebuild/bin/s2n_setup_env.sh

# override SAW_INSTALL_DIR so the downloaded saw goes somewhere else
SAW=false SAW_INSTALL_DIR=tmp-saw ./codebuild/bin/install_default_dependencies.sh

# These copies use the SAW_INSTALL_DIR from s2n_setup_env.sh.
# The /saw-bin they copy from is provided by ../docker-compose.yml.
cp /saw-bin/saw "$SAW_INSTALL_DIR"/bin/saw
cp /saw-bin/abc "$SAW_INSTALL_DIR"/bin/abc
cp /saw-bin/yices "$SAW_INSTALL_DIR"/bin/yices
cp /saw-bin/yices-smt2 "$SAW_INSTALL_DIR"/bin/yices-smt2
#cp /saw-bin/z3-4.8.8 "$SAW_INSTALL_DIR"/bin/z3
cp /saw-bin/z3 "$SAW_INSTALL_DIR"/bin/z3
"$SAW_INSTALL_DIR"/bin/saw --version
"$SAW_INSTALL_DIR"/bin/abc -h || true  # exits 1 on -h, sigh
"$SAW_INSTALL_DIR"/bin/yices --version
"$SAW_INSTALL_DIR"/bin/z3 --version

export CFLAGS=-Wno-error=array-parameter
export CLANG=clang
export LLVMLINK=llvm-link
export SAW_SOLVER_CACHE_PATH=/saw-cache
"$SAW_INSTALL_DIR"/bin/saw --clean-mismatched-versions-solver-cache
exec codebuild/bin/s2n_codebuild.sh
