#!/usr/bin/env bash
set -xe

export IN_SAW_CI=yes

cd /workdir
./scripts/install.sh
cp /saw-bin/cryptol bin/cryptol
cp /saw-bin/saw bin/saw
cp /saw-bin/abc bin/abc
cp /saw-bin/yices bin/yices
# Z3 4.8.14 has been known to nondeterministically time out with the BLST
# proofs, so fall back to 4.8.8 instead. See #1772.
#cp /saw-bin/z3-4.8.8 bin/z3
cp /saw-bin/z3 bin/z3

export PATH=/workdir/bin:$PATH
export CRYPTOLPATH=/workdir/cryptol-specs:/workdir/spec
export SAW_SOLVER_CACHE_PATH=/saw-cache
saw --clean-mismatched-versions-solver-cache

abc -h || true
z3 --version
yices --version
yices-smt2 --version

./scripts/build_x86.sh
./scripts/build_llvm.sh

saw proof/memory_safety.saw

./scripts/check.sh | if grep False; then exit 1; fi
