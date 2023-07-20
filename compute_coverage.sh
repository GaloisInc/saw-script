#!/usr/bin/env bash
set -Eeuxo pipefail

# TODO: Document how to use this, including how to build with coverage enabled
# and run intTests to match the CI. Be sure to note that this file is more
# general than just intTests and can be used for any test suite

# Combine .tix files
SUM_TIX="all.tix"
hpc sum --output=$SUM_TIX --union --exclude=Main --exclude=GitRev $(find . -name "*.tix")

# Generate report
HPC_ROOT=$(find dist-newstyle -name "hpc")
HPC_ARGS=""
for dir in ${HPC_ROOT}/vanilla/mix/*; do
  HPC_ARGS="${HPC_ARGS} --hpcdir=${dir}"
done
hpc report ${HPC_ARGS} ${SUM_TIX}
hpc markup --destdir=hpc_html ${HPC_ARGS} ${SUM_TIX}

