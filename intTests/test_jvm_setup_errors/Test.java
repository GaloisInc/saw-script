class Test
{
    long val;

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
}
