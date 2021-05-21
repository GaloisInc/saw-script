class Test
{
    long val;
    static long counter;

    long get () {
        return val;
    }
    void set (long x) {
        val = x;
    }
    boolean lessThan (Test t) {
        return val < t.val;
    }
    static long lookup (long arr[], int idx) {
        return arr[idx];
    }
    static long next () {
        counter = counter + 1;
        return counter;
    }
}
