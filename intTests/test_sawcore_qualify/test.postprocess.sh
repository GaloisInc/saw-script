# postprocessor for test.saw
# usage: ... | sh test.postprocess.sh | ... per test-and-diff.mk
#
# The output specifically exposes the SAWCore term serial numbers, and
# so it generates several identifiers of the form [xy]`NNNN; these are
# unstable (they change anytime anything rearranges any of the
# bindings in the SAWCore prelude or SAWCore Cryptol module) so
# substitute fixed strings for them. Then also check that the ones
# that are supposed to be the same actually are.
#
# It also assumes any `[0-9][0-9][0-9]+ is something we should
# substitute. For the time being at least, that's true. It's
# important not to match ones with only 1 digit, and for safety
# we also don't match ones with 2; those are display numbers, not
# the internal serial numbers.
#

awk '
   BEGIN {
       counter = 0;
   }
   {
       while ($0 ~ "`[0-9][0-9][0-9]+") {
           # Extract the serial number.
           # Vanilla awk does not support substituting submatches,
           # so just substituting away the rest of the string does
           # not really work. Do something else instead.
           pos = match($0, "`[0-9][0-9][0-9]+");
           serial = substr($0, pos, RLENGTH);

           names[++counter] = serial;
           newname = sprintf("<%d>", counter);
           sub("`[0-9][0-9][0-9]+", newname, $0);
       }
       print;
   }
   END {
       printf "Postprocess found %d serial numbers:\n", counter;
       for (i=1;i<=counter;i++) {
           for (j=i+1;j<=counter;j++) {
               r = (names[i] == names[j]) ? "same" : "different";
               printf "   <%d> == <%d>: %s\n", i, j, r;
           }
       }
   }
'
