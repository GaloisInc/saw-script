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
#    - produce a postprocessed T.log
#    - diff T.log against T.log.good to produce T.diff
#
# It will also test all SAW repl scripts (*.isaw) it finds:
#    - run "saw -B T.isaw"
#    - produce T.rawlog
#    - produce a postprocessed T.log
#    - diff T.log against T.log.good to produce T.diff
#
# Don't use the same names for *.saw and *.isaw files.
#
# If a file named T.saw exists and a file named T.stdin _also_ exists,
# it will run "saw T.saw < T.stdin". This is a special-case hack for
# providing input to certain tests that exercise interactive subshells
# and shouldn't be used otherwise.
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
# generating an error or an empty list.
TESTS=
for SCRIPT in *.saw; do
    if [ "$SCRIPT" = "*.saw" ]; then
        break
    fi
    BASE=${SCRIPT%.saw}
    TESTS="$TESTS $BASE"
done
for SCRIPT in *.isaw; do
    if [ "$SCRIPT" = "*.isaw" ]; then
        break
    fi
    BASE=${SCRIPT%.isaw}
    TESTS="$TESTS $BASE"
done
if [ "$TESTS" = "" ]; then
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
        if [ -f "$TEST.saw" ] && [ -f "$TEST.stdin" ]; then
            echo "$SAW $TEST.saw < $TEST.stdin"
            $SAW $TEST.saw < $TEST.stdin\
                 > $TEST.rawlog 2>&1 || echo FAILED >> $TEST.rawlog
        elif [ -f "$TEST.saw" ]; then
            echo "$SAW $TEST.saw"
            $SAW $TEST.saw > $TEST.rawlog 2>&1 || echo FAILED >> $TEST.rawlog
        else
            echo "$SAW -B $TEST.isaw"
            $SAW -B $TEST.isaw > $TEST.rawlog 2>&1 || echo FAILED >> $TEST.rawlog
        fi

        # Prune any "sawscript> " or "proof (N)> " prompt from the
        # beginnings of lines first. These will appear when feeding
        # stdin to interactive subshells, and removing them up front
        # avoids needing further special-case logic below. Sometimes
        # more than one appears, if we match one try again. I
        # apologize for writing a sed script that branches (the ':'
        # command is a label, and the 't' command branches to a label
        # if any substitution has happened on this input line since
        # the last 't'), but just adding the g flag to the
        # substitution isn't good enough.
        #
        # Furthermore, prune the line number from the results of
        # hitting the Haskell "error" function. SAW isn't supposed to
        # use "error", but it does, and some things trigger it, and
        # having the source line number in the reference outputs is
        # super aggravating because it changes all the time, usually
        # when you aren't expecting it.
        sed < $TEST.rawlog '
            :again
            /^sawscript> /s/^sawscript> //
            /^proof ([0-9][0-9]*)> /s/^proof ([0-9][0-9]*)> //
            tagain

            /^  error, called at [^ :]*\.hs:[0-9:]* in saw-/s/\.hs:.*/.hs/
        ' | (
            # If there's a custom postprocess script for this test,
            # chain it in.
            if [ -f $TEST.postprocess.sh ]; then
                ${TEST_SHELL:-bash} $TEST.postprocess.sh
            else
                cat
            fi
        ) | (
            # If we are on Windows, patch up the output file. The
            # reference files grow carriage returns when checked out
            # because git thinks they're text files; however, ghc
            # binaries apparently do not create output with carriage
            # returns so if we want the output to match we need to
            # insert them.
            #
            # Also, some pathnames get printed with backslashes or a
            # mixture of backslashes and forward slashes. Fix those
            # up. Try to match enough context to not just substitute
            # all backslashes willy-nilly, as that would probably
            # cause other problems. In certain cases we even get "D:\\",
            # and for things to match that needs to be changed to "/d/".
            #
            # MSYS_NT is what the GH Windows runners produce. The
            # other patterns are precautionary.
            case "$(uname -s)" in
                MSYS_NT-*|[Ww]indows*|*[Cc]ygwin*|*[Ii]nterix*)
                    sed '
                        /error, called at/s,\\,/,g
                        /at.*\.cry:[0-9]/s,\\,/,g
                        /PosPair.*posBase =/s,\\\\,/,g
                        /PosPair.*posBase =/s,"C:,"/c,
                        /PosPair.*posBase =/s,"D:,"/d,
                        /PosPair.*posBase =/s,"E:,"/e,
                        /PosPair.*posBase =/s,"F:,"/f,
                        /[^\r]$/s/$/\r/;/^$/s/$/\r/
                    '
                    ;;
                *)
                    cat
                    ;;
            esac
        ) | (
            # We also need to shorten pathnames that contain the
            # current directory, because saw feels the need to expand
            # pathnames (see also saw-script #2082).
            #
            # In addition to that we also need to remove the current
            # directory when it appears in double quotes, at least for
            # now, because many error prints at the saw-core level
            # seem to use default Show instances and the saw-core
            # positions carry the directory and filename separately.
            # This becomes "interesting" from a quoting perspective...
            #
            # This transform must come after the Windows-specific
            # processing because the latter needs to be able to change
            # pathnames so they'll match $CURDIR.
            sed '
                s,'"$CURDIR"'/,,g
                s,"'"$CURDIR"'",".",g
            '
        ) > $TEST.log 

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
