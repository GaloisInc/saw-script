class Test
{
    static int a;
    int b;

    public void set(int x) {
        a = x;
        b = x;
    }
    public int test_a(int x) {
        set(x);
        return a;
    }
    public int test_b(int x) {
        set(x);
        return b;
    }
}
