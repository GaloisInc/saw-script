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
# Avoid tripping on an existing all.tix from a prior run
SUM_TIX="all.tix"
hpc sum --output=$SUM_TIX --union --exclude=Main --exclude=GitRev \
        $(find . ! -path ./all.tix -name "*.tix" -print)

# Find the HPC dir, and don't trip on old versions after a version bump.
# See saw-script #2114.
#
# There is no direct way to do this. Instead, fetch the name of the
# SAW executable. This gives us a path into the build directory for
# the current version:
#    dist-newstyle/build/$TARGET/ghc-$GHC/saw-script-$VERSION/build/saw/saw
#
# where we don't want to have to try to figure out $TARGET, $GHC, or $VERSION.
#
# The hpc dir we want lives under the saw-script-$VERSION dir, but can be in
# different places with different versions of the tooling. So start there and
# then use find.
#
# -v0 (verbosity 0) prevents cabal from accidentally including extraneous
# data (see saw-script #2103)
SAW=$(cabal list-bin -v0 exe:saw)
SAWSCRIPT=$(echo "$SAW" | sed 's,/build/saw/saw$,,')
HPC_ROOT=$(find "$SAWSCRIPT" -name "hpc" -print)

# Check if it actually exists, in case it doesn't, and bail with an error
# message instead of generating hpc's usage message.
if ! [ -d "$HPC_ROOT" ]; then
    echo "$0: no HPC dir found" 1>&2
    exit 1
fi

# Now generate the report
HPC_ARGS=""
for dir in "$HPC_ROOT"/vanilla/mix/*; do
  HPC_ARGS="${HPC_ARGS} --hpcdir=${dir}"
done
hpc markup --destdir=hpc-html ${HPC_ARGS} ${SUM_TIX}
