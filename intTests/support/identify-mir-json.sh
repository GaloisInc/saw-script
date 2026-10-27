#!/bin/sh
# identify-mir-json.sh - extract version strings for mir-json
# usage: identify-mir-json.sh | ...

# First, get the version output from mir-json. This actually prints
# the rustc version and not the mir-json version; we want that info,
# though.
mir-json --version
if [ $? != 0 ]; then
    echo '$0: mir-json --version failed' 1>&2
    echo 'Unknown mir-json: --version failed'
    exit 1
fi

# Function to extract the timestamp for a file.
#
# Linux stat(1) accepts -c for format, and the format is %y.
# BSD stat(1) accepts -f for format, and the format is %Sm.
dostat() {
    case $(uname -s || echo unknown) in
        Linux)
            stat -c %y "$@"
            ;;
        *BSD|Darwin)
            # "Darwin" is MacOS
            stat -f %Sm "$@"
            ;;
        *)
            # Even with LC_ALL=C this may not print the right fields,
            # and with traditional ls it won't print the year for
            # recent dates. But it's better than failing entirely.
            LC_ALL=C ls -ld "$@" | awk '{ print $6, $7, $8 }'
            ;;
    esac
}

# Get its timestamp.
# Note: type -p to print just the path is a bashism, and doesn't
# work in dash or ash-derived shells.
#
# Normal shells will print "mir-json is ..." but bash likes to say
# "mir-json is cached (path)" instead, just to make things more
# exciting. Get the last word in the output, and then strip off
# any parens.
#
# Don't print the path to mir-json as that may expose internal config
# on people's devel machines.
LOCATION=$(type mir-json | awk '{ print $NF }' | sed 's/^(//;s/)$//')
TIMESTAMP=$(dostat "$LOCATION")
echo "mir-json mtime: $TIMESTAMP"

# Now, we want the mir-json version as well. This is not so easy,
# because there's no way to get it from the executable. See mir-json
# #77.
#
# First, extract the cargo-level version from cargo. There doesn't
# seem to be any way to get information about installed stuff from
# cargo other than telling it to dump all of it and searching the
# results.
INFO=$(cargo install --list | grep '^mir-json ')
case "$INFO" in
    mir-json\ v*\ \(*\):)
        ;;
    *)
        echo "$0: Unexpected output from cargo install --list" 1>&2
        echo "$0: Got: $INFO" 1>&2
        echo 'Further version details unknown'
        exit 1
esac

# Output the first two words (mir-json v1.5) as part of the version data.
echo "$INFO" | awk '{ print "mir-json version from cargo:", $1, $2 }'

# The third word is, apparently, the source dir mir-json got built from.
# It is not a given that this is pointing at the same commit as it was
# when mir-json got built, but it's the best we can readily do. If this
# becomes a problem, fix mir-json #77. It would be sufficient, for
# example, to install a mir-json-version shell script with the commit
# hash and date baked into it.
MJDIR=$(echo "$INFO" | awk '{ print $3 }' | sed 's/:$//;s/^(//;s/)$//')
if ! [ -d "$MJDIR" ]; then
    echo "$0: Source directory $MJDIR does not exist" 1>&2
    echo 'Further version details unknown'
    exit 1
fi

cd "$MJDIR"
git log --max-count=1 --date=format:%c --pretty=format:'probable mir-json commit: %H from %ad and/or %cd%n'
if [ $? != 0 ]; then
    echo "$0: git log failed" 1>&2
    echo "git log failed: Further version details unknown"
    exit 1
fi

exit 0
