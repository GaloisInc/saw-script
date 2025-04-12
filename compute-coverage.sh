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
hpc sum --output=$SUM_TIX --union --exclude=Main --exclude=SAWVersion.GitRev \
        $(find . ! -path ./all.tix -name "*.tix" -print)

# Find the HPC dir, and don't trip on old versions after a version bump.
# See saw-script #2114.
#
# There is no direct way to do this. Instead, first fetch the name of
# the SAW executable. This gives us a path into the build directory
# (somewhere in dist-newstyle) for the current version.
#
# -v0 (verbosity 0) prevents cabal from accidentally including extraneous
# data (see saw-script #2103)
SAW=$(cabal list-bin -v0 exe:saw)

# Now what we want is the top-level build dir for the saw package.
# As of when #2114 was merged, the path we were getting was:
#
#    dist-newstyle/build/$TARGET/ghc-$GHC/saw-script-$VERSION/build/saw/saw
#
# While developing #2280 ("reorganize the tree") and #2283 (having
# build.sh generate GitRev.hs) (note: #2280 comes after #2283 despite
# the numbering) things changed. It appears that moving from a
# "custom" Cabal build to a "simple" one in #2283 changes things so we
# now get:
#
#    dist-newstyle/build/$TARGET/ghc-$GHC/saw-script-$VERSION/x/saw/build/saw/saw
#
# with an extra "x/saw", and then #2280 changes the name of the top-level
# package from "saw-script" to "saw" so we get this:
#
#    dist-newstyle/build/$TARGET/ghc-$GHC/saw-$VERSION/x/saw/build/saw/saw
#
# In order to handle this, I'm going to first prune build/saw/saw off
# the end (as in #2114), and then (if it's there) also prune
# x/saw. Then, if the directory ends in something matching saw-*, go
# ahead, and otherwise bail out and ask for help instead of chugging
# on and maybe making a mess.
#
# Alternatively, we could extract the current version from saw.cabal
# and run find to get the saw-$VERSION dir in dist-newstyle. (Note
# that ci.sh already extracts the version and it's not particularly
# difficult or fragile. Trying to figure $TARGET or $GHC would be
# messy, but we still wouldn't need to do that.)
BUILDDIR=$(echo "$SAW" | sed 's,/build/saw/saw$,,;s,/x/saw$,,')

case "$BUILDDIR" in
    */saw-*.*) ;;
    *)
        echo "$0: Cannot figure the build directory to find hpc dirs" 1>&2
        echo "$0: The saw executable is here: $SAW" 1>&2
        echo "$0: I see the following possibly-matching hpc material:" 1>&2
        find dist-newstyle -type d | grep '/saw-' | grep '/hpc/vanilla/mix' 1>&2
        echo "$0: ...help?" 1>&2
        exit 1
esac

# As of #2114 given the build directory we wanted to find the HPC dir
# in it:
#    The hpc dir we want lives under the saw-script-$VERSION dir, but
#    can be in different places with different versions of the tooling.
#    So start there and then use find.
#
# As of #2283 we get separate build directories for the saw executable
# and the saw-script library in the toplevel package, and then in
# #2280, we apparently get a separate build directory for each
# sublibrary too. Furthermore, even though before it was apparently
# sufficient to find the saw executable's build info, now it seems we
# need all the pieces to be able to do a successful hpc report
# generation.
#
# Also, it seems that what we want is every directory in each
# hpc/vanilla/mix. The previous version of this code looked for a
# single 'hpc' dir and then iterated through its hpc/vanilla/mix; here
# what we'll do is just find all hpc/vanilla/mix/* dirs.

HPC_ARGS=""
for d1 in $(find "$BUILDDIR" -path '*/hpc/vanilla/mix' -type d -print); do
    for d2 in "$d1"/*; do
        if [ "$d2" = "$d1/*" ]; then
            continue
        fi
        HPC_ARGS="${HPC_ARGS} --hpcdir=${d2}"
    done
done

# Check if we actually found stuff, in case we didn't, and bail with
# an error message instead of generating hpc's usage message.
if [ "x$HPC_ARGS" = x ]; then
    echo "$0: Found no paths matching hpc/vanilla/mix/* in $BUILDDIR" 1>&2
    echo "$0: There are the following hpc dirs:" 1>&2
    find "$BUILDDIR" -type d -name hpc -print 1>&2
    echo "$0: and the following contents:" 1>&2
    find $(find "$BUILDDIR" -type d -name hpc -print) -type f -print 1>&2
    echo "$0: ...help?" 1>&2
    exit 1
fi
    
hpc markup --destdir=hpc-html ${HPC_ARGS} ${SUM_TIX}
