# Don't exit randomly
set +e

# Fail immediately if the two reference outputs have become the
# same. There's two on purpose, because there's two solutions, and the
# solver will sometimes return one and sometimes the other.

if diff test.log.1.good test.log.2.good >/dev/null 2>&1; then
    echo "$0: The two reference outputs are the same." 1>&2
    echo "$0: Please correct that." 1>&2
    exit 1
fi

#
# This is a hacked subset of what's in support/test-and-diff.sh
# because we need to be able to check either of two reference outputs.
# FUTURE: update test-and-diff to support that.
#
# to clean: rm -f test.log test.rawlog *.diff
# 

# run the test
$SAW test.saw > test.rawlog 2>&1 || echo FAILED >> test.rawlog

# Prune the timestamps and current directory. If we are running
# on Windows, _insert_ carriage returns. See test-and-diff.sh
# for further explanation.
CURDIR=$(pwd -P || pwd)
sed < test.rawlog '
    /^\[[0-9][0-9]:[0-9][0-9]:[0-9][0-9]\.[0-9][0-9][0-9]\] /{
        s/^..............//
    }
    s,'"$CURDIR"'/,,
    s,\(solverStatsGoalSize.=.\)[0-9N]*,\1N,g
' | (
    case "$(uname -s)" in
        MSYS_NT-*|[Ww]indows*|*[Cc]ygwin*|*[Ii]nterix*)
            sed '/[^\r]$/s/$/\r/;/^$/s/$/\r/'
            ;;
        *)
            cat
            ;;
    esac
) > test.log

# diff
diff -u test.log.1.good test.log > test.log.1.diff 2>&1
diff -u test.log.2.good test.log > test.log.2.diff 2>&1

# If both diffs are nonempty, we failed.
if [ -s test.log.1.diff ] && [ -s test.log.2.diff ]; then
    echo "*** diff 1:"
    cat test.log.1.diff
    echo "*** diff 2:"
    cat test.log.2.diff
   
    cat 1>&2 <<EOF
Unexpected test diffs.
If the new output is correct, update the reference outputs, but
please don't do so without thinking. Be sure to make corresponding
updates to all the reference outputs.
EOF

    # We failed.
    exit 1
fi

# done
exit 0
