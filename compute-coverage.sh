#!/usr/bin/env bash
set -Eeuxo pipefail

# This script generates an HTML coverage report for any tests run within the
# saw-script repo. Follow these steps to use it:
# 1. Build with coverage enabled. One way to do this is to add "coverage: true"
#    to the saw-script package in cabal.project.
# 2. Run whatever tests you want. The only caveat is that this script will only
#    work if saw is invoked with a working directory somewhere in this repo.
# 3. Run this script.
# 4. You'll find the HPC HTML report in the "hpc-html" directory.

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

