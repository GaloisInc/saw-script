#!/usr/bin/env bash
set -xe

cd /workdir
./scripts/install.sh
cp /saw-bin/cryptol bin/cryptol
cp /saw-bin/saw bin/saw
cp /saw-bin/abc bin/abc
cp /saw-bin/yices bin/yices
# Z3 4.8.14 has been known to nondeterministically time out with the BLST
# proofs, so fall back to 4.8.8 instead. See #1772.
cp /saw-bin/z3-4.8.8 bin/z3

export PATH=/workdir/bin:$PATH
export CRYPTOLPATH=/workdir/cryptol-specs:/workdir/spec

abc -h || true
z3 --version
yices --version
yices-smt2 --version

./scripts/build_x86.sh
./scripts/build_llvm.sh

SAW_SOLVER_CACHE_PATH=/blst.cache saw proof/memory_safety.saw
echo "LOOK HERE @m-yac"
echo "print_solver_cache_stats" | saw

./scripts/check.sh | if grep False; then exit 1; fi
