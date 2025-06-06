#!/bin/sh
# savegitinfo.sh - extract git information and generate GitRev.hs
# usage: saw-version/src/SAWVersion/savegitinfo.sh
#

# Setting the environment variable SAW_SUPPRESS_GITREV to something
# nonempty suppresses updating GitRev.hs.
#
# This should obviously not be done for production builds and is not
# recommended when one is _using_ SAW, because even if one is fairly
# careful it is still possible to get confused about when you last
# recompiled and exactly which version that was, plus when reporting
# bugs you want to be able to report the version accurately.
#
# However, when one is actively _developing_ SAW, the version you're
# using is essentially always the one you just built, and if it panics
# the version info in the panic message isn't especially informative.
# Meanwhile, keeping that message up to date incurs a lot of build
# time, because among other things every git change causes a rebuild
# of the SAWCore prelude (so the Template Haskell executes with the
# latest code, which is good in general but quite pointless when all
# that's changed is the git hash in the panic string) and this is
# quite slow.
#
# So, because it's preferable to other possible mechanisms for
# suppressing that rebuild, we provide an escape hatch. Use at your
# own risk.
#
# Note that while in theory the version string might cue you to notice
# that you forgot to recompile before testing, which is why e.g.
# traditionally Unix kernels print a build serial number when you boot
# them, this isn't at all effective with hashcode versions so there's
# no point.


set -e
unset CDPATH   # `./` ensure no echoing of current directory in output
WHERE=$(dirname "$0")

# Run "git describe" in directory $1 and wrap the output in Maybe
gitdescribe() {
    local output

    # Note: we get Nothing back if cd fails
    # Note: cd inside `output=` ensures no extraneous output from errors.
    output=$(cd ./$1 && git describe --always --dirty)
      # `./` reduces echoing of current directory when CDPATH is set.
    if [ $? != 0 ]; then
        echo Nothing
    else
        echo 'Just "'"$output"'"'
    fi
}

# Run "git branch" and wrap the output in Maybe
gitbranch() {
    local output

    output=$(git branch --points-at HEAD)
    if [ $? != 0 ]; then
        echo Nothing
    else
        # Strip off the leading "  " or "* "
        # and in casae we get more than one, combine on one line
        output=$(echo "$output" | sed 's/^..//' | tr '\n' ' ' | sed 's/ $//')
        echo 'Just "'"$output"'"'
    fi
}

# Run "git log" to get the last change affecting a subtree
# (which should be the first argument)
gitlog() {
    output=$(git log --max-count=1 --pretty=format:%h -- $1)
    if [ $? != 0 ]; then
        echo Nothing
    else
        echo 'Just "'"$output"'"'
    fi
}

# Generate GitRev.hs
generate() {
    local foundgit=$1
    local sawhash=$2
    local sawbranch=$3
    local aighash=$4
    local what4hash=$5
    local rmehash=$6

    cat > "$WHERE"/GitRev.hs.new <<- EOF
	module SAWVersion.GitRev where
	-- | Whether git was found at compile time, which affects how we
	--   interpret Nothing in the data below
	foundGit :: Bool
	foundGit = $foundgit
	-- | The git commit hash for the HEAD of saw-script at compile-time
	hash :: Maybe String
	hash = $sawhash
	-- | The git branch string for the HEAD of saw-script at compile-time
	branch :: Maybe String
	branch = $sawbranch
	-- | String describing the HEAD of the deps/aig submodule at compile-time
	aigHash :: Maybe String
	aigHash = $aighash
	-- | String describing the HEAD of the deps/what4 submodule at compile-time
	what4Hash :: Maybe String
	what4Hash = $what4hash
	-- | String describing the most recent commit which modified the rme directory
	-- at compile-time
	rmeHash :: Maybe String
	rmeHash = $rmehash
EOF
    if diff -q "$WHERE"/GitRev.hs "$WHERE/"GitRev.hs.new >/dev/null 2>&1; then
        echo 'GitRev unchanged'
        rm -f "$WHERE"/GitRev.hs.new
    else
        echo 'Updated GitRev'
        mv -f "$WHERE/"GitRev.hs.new "$WHERE"/GitRev.hs
    fi
}

# If .git is not here and we already have a GitRev.hs, assume it
# contains useful info and don't clobber it with a new one that won't.
if ! [ -d .git ] && [ -f "$WHERE"/GitRev.hs ]; then
    echo 'Keeping existing GitRev; no .git directory'
    exit 0
fi

# If SAW_SUPPRESS_GITREV is set and we already have a GitRev.hs, leave
# it alone, whether or not it's current.
if [ "x$SAW_SUPPRESS_GITREV" != x ] && [ -f "$WHERE"/GitRev.hs ]; then
    echo 'Keeping existing GitRev; SAW_SUPPRESS_GITREV is set'
    exit 0
fi

# Check for git being here
GITVER=$(git --version 2>/dev/null || echo MISSING)
case "$GITVER" in
    git*)
        SAWHASH=$(gitdescribe .)
        SAWBRANCH=$(gitbranch)
        AIGHASH=$(gitdescribe deps/aig)
        WHAT4HASH=$(gitdescribe deps/what4)
        RMEHASH=$(gitlog rme)
        generate True "$SAWHASH" "$SAWBRANCH" "$AIGHASH" "$WHAT4HASH" "$RMEHASH"
    ;;
    MISSING)
        generate False Nothing Nothing Nothing Nothing Nothing
    ;;
    *)
        echo "$0: Did not understand git --version output:" 1>&2
        echo "   $GITVER" 1>&2
        echo "Help?" 1>&2
        exit 1
    ;;
esac

# done
exit 0
