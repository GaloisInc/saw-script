class Test
{
    // This function is adapted from the example in
    // https://github.com/GaloisInc/saw-script/issues/2740, and its verification
    // is expected to be tractable iff path satisfiability checking is enabled
    // in SAW.
    public static long f(long i) {
        long x = i;

        for (long j = i; j < Long.MIN_VALUE + 1; j++) {
            x += 1;
        }

        return x;
    }
}
