#!/usr/bin/env bash
set -xe

export IN_SAW_CI=yes

cd /saw-script/aws-lc-verification/SAW
./scripts/install.sh
rm -f bin/saw
cp /saw-bin/saw bin/saw
cp /saw-bin/abc bin/abc
cp /saw-bin/yices bin/yices
# Z3 4.8.14 has been known to nondeterministically time out with the BLST
# proofs, so fall back to 4.8.8 instead. See #1772.
#cp /saw-bin/z3-4.8.8 bin/z3
cp /saw-bin/z3 bin/z3

export PATH=/saw-script/aws-lc-verification/SAW/bin:$PATH
export CRYPTOLPATH=/saw-script/aws-lc-verification/cryptol-specs
export SAW_SOLVER_CACHE_PATH=/saw-cache
saw --clean-mismatched-versions-solver-cache

./scripts/entrypoint_check.sh

