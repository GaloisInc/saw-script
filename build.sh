#!/bin/sh
# build.sh: build SAW
# usage: ./build.sh [-j jobs] [target]
#
# Valid targets are:
#    build (the default)
#    gitrev (included in build, needed before building)
#    submodules (included in build, at least for now)
#    test
#       integration-tests
#       other-tests
#    clean
#
# Setting environment variable SAW_SUPPRESS_GITREV suppresses updating
# GitRev.hs. See savegitinfo.sh.

set -e

JOBS=''
case "x$1" in
    x-j)
        if [ $# -lt 2 ]; then
            echo "$0: -j expects an argument" 1>&2
            exit 1
        fi
        shift; JOBS=$1; shift
        ;;
    x-j*)
        JOBS=${1#-j}; shift
        ;;
    *)
        ;;
esac
if [ "x$JOBS" != x ]; then
    # test this with -ge so if $JOBS isn't a number the test will fail
    # and we'll take the error branch
    if [ "$JOBS" -ge 1 ] 2>/dev/null; then
        JOBSOPT="-j$JOBS"
    else
        echo "$0: invalid job count $JOBS" 1>&2
        exit 1
    fi
else
    JOBSOPT=''
fi

# Keep the list of tests in sync. There are three lists of tests:
#   - here
#   - doc/developer/developer.md
#   - and of course the definitions in the *.cabal files
#
OTHERTESTS='
   saw-core-tests
   crux-mir-comp-tests
   cryptol-saw-core-tests
   saw-core-rocq-tests
   saw-core-isabelle-tests
'
ALLTESTS="integration-tests $OTHERTESTS"
TESTSUITES=$(echo "$ALLTESTS" | tr '\n' ' ' | sed 's/^/test-suite:/')

##############################
# gitrev

tgt_gitrev() {
    # fetch/update the compiled-in git version info
    saw-version/src/SAWVersion/savegitinfo.sh
}

##############################
# submodules

tgt_submodules() {
    echo "git submodule update --init"
    git submodule update --init
}

##############################
# build

install() {
  PROG=$(cabal list-bin -v0 exe:$1)
  echo "cp $PROG bin/"
  cp $PROG bin/
}

tgt_build() {
    tgt_gitrev
    tgt_submodules

    # Note that although we don't include the cryptol-remote-api executables in
    # binary distributions, it is nevertheless worthwhile to build them here to
    # ensure that they are compatible with the particular submodule commits in
    # use.

    echo "cabal build $JOBSOPT ..."
    cabal build $JOBSOPT \
                exe:cryptol exe:cryptol-remote-api exe:cryptol-eval-server \
                exe:saw exe:saw-remote-api \
                exe:crux-mir-comp exe:css exe:extcore-info exe:verif-viewer \
                exe:cryptol-to-isabelle \
                $TESTSUITES

    echo "rm -rf bin && mkdir bin"
    rm -rf bin && mkdir bin

    install cryptol
    install saw
    install saw-remote-api
    install crux-mir-comp
    install extcore-info
    install verif-viewer
    install cryptol-to-isabelle

    echo
    echo "COPIED EXECUTABLES TO `pwd`/bin."
}

##############################
# tests

runtests() {
    local test
    local bad=0

    set +e
    for test in "$@"; do
        (
            # While you can "cabal run test-suite:crux-mir-comp-tests"
            # from the top level of the tree... if you do, it quietly
            # skips all the actual tests and "succeeds". It needs to
            # be run from the crux-mir-comp subdir.
            if [ "$test" = crux-mir-comp-tests ]; then
                echo "cd crux-mir-comp"
                cd crux-mir-comp
            fi
            echo "cabal run test-suite:$test"
            cabal run test-suite:$test
        )
        if [ $? != 0 ]; then
            echo "$0: $test failed" 1>&2
            bad=1
        fi
    done
    set -e
    if [ $bad != 0 ]; then
        echo "$0: Tests failed" 1>&2
        exit $bad
    fi
}

tgt_integrationtests() {
    runtests integration-tests
}

tgt_othertests() {
    runtests $OTHERTESTS
}

tgt_tests() {
    runtests $ALLTESTS
}

##############################
# clean

tgt_clean() {
    echo "cabal clean"
    cabal clean
    if [ -d bin ]; then
        echo "rm -rf bin"
        rm -rf bin
    fi
}

##############################
# top level

case "X$1" in
    Xgitrev) tgt_gitrev;;
    Xsubmodules) tgt_submodules;;
    X|Xbuild) tgt_build;;
    Xintegration-tests) tgt_integrationtests;;
    Xother-tests) tgt_othertests;;
    Xtest|tests|all-tests) tgt_test;;
    Xclean) tgt_clean;;
    *)
        echo "$0: Don't know how to build $1" 1>&2
        exit 1
        ;;
esac
exit 0
