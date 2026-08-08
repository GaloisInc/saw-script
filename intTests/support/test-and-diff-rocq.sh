# test-and-diff-rocq.sh: variant test-and-diff for the Rocq exporter tests.
#
# usage: sh ../../intTests/support/test-and-diff.sh [verb]
# where [verb] is the same as in the base test-and-diff.
#
# This version runs all SAW files *.saw like test-and-diff. But it
# also expects each one to generate some number of output .v files; it
# also diffs those against reference versions.
#
# The output .v files must be numbered using the form foo_1.v,
# foo_2.v, etc. The files foo_1.v.good and foo_2.v.good should
# correspondingly exist. The numbering starts at 1.
#
# Alternatively they can be named foo_{1,2,3,...}_prove0.v.
#
# It does not support SAW repl scripts (*.isaw) for simplicity, nor
# does it support output filtering stuff that isn't relevant to this
# use case.
#
# Note: we assume all .v files are test output and the clean rule may
# clobber them. Don't put your own handwritten files in the test dir.

# Get the list of tests.
#
# Note that in some shells (and depending on settings) asking for
# *.saw when there aren't any will yield "*.saw" rather than
# generating an error or an empty list.
TESTS=
for SCRIPT in *.saw; do
    if [ "$SCRIPT" = "*.saw" ]; then
        break
    fi
    BASE=${SCRIPT%.saw}
    TESTS="$TESTS $BASE"
done
if [ "$TESTS" = "" ]; then
    echo "$0: Found no files matching *.saw" 1>&2
    exit 1
fi

# shell function for the run-tests op
run-tests() {
    for TEST in $TESTS; do
        # Remove any existing test.log first as a precaution. This
        # protects against misreading the results if the whole run
        # gets killed before a new test.log gets produced.
        # Also remove any corresponding .v files.
        rm -f $TEST.log
        rm -f ${TEST}_*.v

        # run the test
        # (do not fail if saw does, instead log it)
        echo "$SAW $TEST.saw"
        $SAW $TEST.saw > $TEST.log 2>&1 || echo FAILED >> $TEST.log

        # Check the output against the expected version.
        # Note: because we (intentionally) aren't using set -e, we
        # don't need to failure-protect this with || true.
        # Send any errors from diff to the output so they get seen.
        diff -u $TEST.log.good $TEST.log > $TEST.log.diff 2>&1
        echo "diff -u $TEST.log.good $TEST.log"

        # Now diff the output .v files. Count up until we get to
        # a number where neither $TEST_$I.v nor $TEST_SI.v.good
        # exists.
        I=1
        while :; do
            TESTX=${TEST}_$I
            TESTY=${TEST}_${I}_prove0
            if [ -f "$TESTX.v" ] || [ -f "$TESTX.v.good" ]; then
                diff -u "$TESTX.v.good" "$TESTX.v" > "$TESTX.v.diff"
                echo "diff -u $TESTX.v.good $TESTX.v"
                I=$(( $I + 1 ))
            elif [ -f "$TESTY.v" ] || [ -f "$TESTY.v.good" ]; then
                diff -u "$TESTY.v.good" "$TESTY.v" > "$TESTY.v.diff"
                echo "diff -u $TESTY.v.good $TESTY.v"
                I=$(( $I + 1 ))
            else
                break
            fi
        done
    done
}

# shell function for the show-diffs op
show-diffs() {
    # We assume all *.diff files belong to us, so we can just do
    # "cat *.diff" rather than iterating over the known filenames.
    cat *.diff
}

# shell function for the check-diffs op
check-diffs() {
    LINES=$(cat *.diff 2>/dev/null | wc -l)
    if [ $LINES -gt 0 ]; then
       cat 1>&2 <<EOF

Unexpected test diffs.
If the new outputs are correct, update the reference outputs, but
please don't do so without thinking.
EOF
       exit 1
    fi
}

# shell function for the good op
good() {
    checkonce () {
        if ! [ -f $1 ]; then
           echo "$0: No test output for $1" 1>&2
           echo "$0: Cannot update reference outputs" 1>&2
           exit 1
        fi
    }
    for TEST in $TESTS; do
        checkonce $TEST.log
        I=1
        while :; do
            TESTX=${TEST}_$I
            TESTY=${TEST}_${I}_prove0
            if [ -f "$TESTX.v" ] || [ -f "$TESTX.v.good" ]; then
                checkonce "$TESTX.v"
                I=$(( $I + 1 ))
            elif [ -f "$TESTY.v" ] || [ -f "$TESTY.v.good" ]; then
                checkonce "$TESTY.v"
                I=$(( $I + 1 ))
            else
                break
            fi
        done
    done

    once () {
        if ! [ -f $1.good ] || \
           ! diff -q $1.good $1 >/dev/null; then
	        echo "cp $1 $1.good"
	        cp $1 $1.good
        fi
    }
    for TEST in $TESTS; do
        once $TEST.log
        I=1
        while :; do
            TESTX=${TEST}_$I
            TESTY=${TEST}_${I}_prove0
            if [ -f "$TESTX.v" ] || [ -f "$TESTX.v.good" ]; then
                once "$TESTX.v"
                I=$(( $I + 1 ))
            elif [ -f "$TESTY.v" ] || [ -f "$TESTY.v.good" ]; then
                once "$TESTY.v"
                I=$(( $I + 1 ))
            else
                break
            fi
        done
    done
}

# shell function for the clean op
clean() {
    echo "rm -f *_[0-9]*.v *.log *.diff"
    rm -f *_[0-9]*.v *.log *.diff
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
