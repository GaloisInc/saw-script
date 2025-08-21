#!/bin/sh
# check-from.sh - check a *.FROM provenance-tracking file
# usage: check-from.sh *.FROM
#
# The format is unindented section headers followed by indented
# section data (on a line-by-line basis).
#
# The allowable sections are:
#    versions (required)
#    versions-notes (optional)
#    persistent-notes (optional)

BAD=0
for F in "$@"; do
    case "$F" in
        *.FROM) ;;
        *) echo "$0: $F: Not named *.FROM" 1>&2; BAD=1; continue;;
    esac
    awk < "$F" '
        { ++lineno; }
        function die(msg) {
            printf "%s:%d: %s\n", f, lineno, msg > "/dev/stderr";
            dead = 1;
            exit(1);
        }
        END { if (dead) exit(1); }

        BEGIN { havesection = 0; haveversions = 0; }
        /^ / && !havesection { die("Data with no section"); }
        /^ / { next; }
        /^$/ { next; }
        /^versions$/ { havesection = haveversions = 1; next; }
        /^versions-notes$/ { havesection = 1; next; }
        /^persistent-notes$/ { havesection = 1; next; }
        { die("Unexpected section " $1); }
        END {
            if (!haveversions) {
                die("No versions section");
            }
        }
    ' "f=$F"
    if [ $? != 0 ]; then
        BAD=1
    fi
done

exit $BAD
