# test-and-diff.sh: run SAW and diff the output against a reference
# copy.
#
# usage: sh ../support/test-and-diff.sh [verb]
# where verb is:
#    test (default)	do run-tests, show-diffs, check-diffs
#    run-tests		run all tests
#    show-diffs		print all (nonempty) diff outputs
#    check-diffs	exit 1 if there are any nonempty diff outputs
#    good		update reference outputs from the current run
#    clean		delete all results and intermediate output
#
# That is, the arguments are akin to make or similar tools.
#
# Note that this file is meant to be run/spawned/exec'd, not sourced.
# It should also be run explicitly with the shell so that the test
# suite is operable on Windows where #! doesn't work.
#
# This script will test all SAW files (*.saw) it finds in its current
# directory, as follows, assuming T.saw is one such file:
#    - run "saw T.saw"
#    - produce T.rawlog
#    - produce T.log with timestamps stripped out
#    - diff T.log against T.log.good to produce T.diff
#
# These steps are "run-tests". It will always run all tests before
# checking any of the outputs. If SAW itself fails (exits non-zero)
# that fact is logged, and if unexpected will cause a diff, but will
# not cause the test run to fail. This allows having tests that are
# expected to fail in SAW, which is important for e.g. checking error
# behavior.
#
# Note: don't write anything that relies on the existence of the
# .rawlog file; one hopes the need for it will eventually go away.
#
# Also note: this script assumes that all *.rawlog, *.log, and *.diff
# files it finds belong to it; they will be deleted at clean time.
# This prevents old outputs to hang around forever when the list of
# tests changes.
#
# It is fine to use this script when you have only one SAW script to
# test. The infrastructure for supporting multiple scripts does not
# cost much.
#
# There is, however, an expectation that if there are multiple scripts
# in one test directory, they are all fast. Having multiple scripts at
# once loses the ability to run them separately or address them
# directly from enclosing test infrastructure. We don't want that to
# incur significant costs or create aggravations.
#
# Note: we could, like make, not rerun tests whose output is newer
# than (all) their inputs. So far I haven't done this. As long as the
# scripts are all fast it probably doesn't matter.
#
# While I've written this script to be careful about spaces, spaces in
# filenames aren't supported. Don't do that; it just creates headaches
# for everyone.
#

# Get the list of tests.
#
# Note that in some shells (and depending on settings) asking for
# *.saw when there aren't any will yield "*.saw" rather than
# generating an error.
TESTS=
for SCRIPT in *.saw; do
    BASE=${SCRIPT%.saw}
    TESTS="$TESTS $BASE"
done
if [ "$TESTS" = " *.saw" ] || [ "$TESTS" = " " ]; then
    echo "$0: Found no files matching *.saw" 1>&2
    exit 1
fi

# Get the current directory, because we'll need to filter it out of
# the saw output. Be sure to get the real current directory. Because
# ksh's silly ideas about symlinks got stuffed into posix, pwd can lie
# and then what it prints won't be the same as what saw outputs.
#
# Don't use the variable PWD for this; it has magic semantics in the
# shell and, for the same reasons, may also lie.
#
# Bomb if the current directory includes a comma (just in case) so we
# can use comma as a delimiter in the seddery below.
CURDIR=$(pwd -P || pwd)
if echo "$CURDIR" | grep -q , >/dev/null; then
    echo "$0: Your current directory name contains a comma." 1>&2
    echo "$0: I can't deal with that. Sorry..." 1>&2
    exit 1
fi

# shell function for the run-tests op
run-tests() {
    for TEST in $TESTS; do
        # Remove any existing test.log first as a precaution. This
        # protects against misreading the results if the whole run
        # gets killed before a new test.log gets produced.
        rm -f $TEST.log

        # run the test
        # (do not fail if saw does, instead log it)
        echo "$SAW $TEST.saw"
        $SAW $TEST.saw > $TEST.rawlog 2>&1 || echo FAILED >> $TEST.rawlog

        # Prune the timestamps from the log since they'll never match.
        # We also need to shorten pathnames that contain the current
        # directory, because saw feels the need to expand pathnames
        # (see also saw-script #2082).
        sed < $TEST.rawlog > $TEST.log '
            /^\[[0-9][0-9]:[0-9][0-9]:[0-9][0-9]\.[0-9][0-9][0-9]\] /{
                s/^..............//
            }
            s,'"$CURDIR"'/,,
        '

        # Check the output against the expected version.
        # Note: because we (intentionally) aren't using set -e, we
        # don't need to failure-protect this with || true.
        # Send any errors from diff to the output so they get seen.
        diff -u $TEST.log.good $TEST.log > $TEST.log.diff 2>&1
    done
}

# shell function for the show-diffs op
show-diffs() {
    # The easy way to do this is just "cat *.diff". While (as
    # documented) above we assume all *.diff files belong to us, don't
    # do things that way, because there isn't an analogous form for
    # check-diffs. Thus if a stray nonempty *.diff file appeared it
    # would show up in the show-diffs output but not cause check-diffs
    # to fail, and that would be quite confusing.
    #
    # As long as the number of tests here isn't really excessive the
    # shell iteration and resulting multiple cat processes won't cost
    # enough to care about.
    for TEST in $TESTS; do
        cat $TEST.log.diff
    done
}

# shell function for the check-diffs op
check-diffs() {
    for TEST in $TESTS; do
        if [ -s $TEST.log.diff ]; then
            cat 1>&2 <<EOF

Unexpected test diffs.
If the new outputs are correct, update the reference outputs, but
please don't do so without thinking.
EOF
            exit 1
        fi
    done
}

# shell function for the good op
good() {
    # This check might be annoying; sometimes you want to update one
    # output at a time or similar. For now assume it's probably a good
    # idea to have it though.
    for TEST in $TESTS; do
        if ! [ -f $TEST.log ]; then
            echo "$0: No test output for $TEST.saw" 1>&2
            echo "$0: Cannot update reference outputs" 1>&2
            exit 1
        fi
    done

    # now actually do it
    for TEST in $TESTS; do
        if ! [ -f $TEST.log.good ] || \
           ! diff -q $TEST.log.good $TEST.log >/dev/null; then
	        echo "cp $TEST.log $TEST.log.good"
	        cp $TEST.log $TEST.log.good
        fi
    done
}

# shell function for the clean op
clean() {
    echo "rm -f *.rawlog *.log *.diff"
    rm -f *.rawlog *.log *.diff
}

# shell function for the test op
test() {
    run-tests
    show-diffs
    check-diffs
}

# run the requested operations
if [ $# = 0 ]; then
    test
else
    for VERB in "$@"; do
        case "$VERB" in
            test)
                test
            ;;
            run-tests)
                run-tests
            ;;
            show-diffs|show) # allow "show" as short form
                show-diffs
            ;;
            check-diffs|check) # allow "check" as short form
                check-diffs
            ;;
            good)
                good
            ;;
            clean)
                clean
            ;;
            *)
                echo "$0: unknown action $VERB" 1>&2
                exit 1
            ;;
        esac
    done
fi

# done
exit 0
