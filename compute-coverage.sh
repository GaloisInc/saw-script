#!/usr/bin/env bash
set -Eeuxo pipefail

# This script generates an HTML coverage report for any tests run within the
# saw-script repo. It uses HPC, which is a tool in the standard GHC
# distribution. Follow these steps to use this script:
# 1. Build with coverage enabled. One way to do this is to add "coverage: true"
#    to the saw-script package in cabal.project.
# 2. Run whatever tests you want. It is important that you use the saw binary
#    built in step (1), and that your current working directory be somewhere at
#    or underneath this top level-directory.
# 3. Run this script in the top-level directory (where this script is found).
# 4. You'll find the HPC HTML report in the "hpc-html" directory beneath the
#    directory containing this script.

# Combine .tix files
SUM_TIX="all.tix"
hpc sum --output=$SUM_TIX --union --exclude=Main --exclude=GitRev $(find . -name "*.tix")

# Generate report
HPC_ROOT=$(find dist-newstyle -name "hpc")
HPC_ARGS=""
for dir in ${HPC_ROOT}/vanilla/mix/*; do
  HPC_ARGS="${HPC_ARGS} --hpcdir=${dir}"
done
hpc markup --destdir=hpc-html ${HPC_ARGS} ${SUM_TIX}
