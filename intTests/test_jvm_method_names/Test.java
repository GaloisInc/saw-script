class Test
{
    long val;

    public Test() {
        val = 0;
    }
    public Test(long x) {
        val = x;
    }
    public Test(int x) {
        val = x;
    }
    public long get() {
        return val;
    }
    public void increment() {
        val = val + 1;
    }
    public void increment(long x) {
        val = val + x;
    }
    public void increment(int x) {
        val = val + (long)x;
    }
    public void increment(Test x) {
        val = val + x.val;
    }
}
