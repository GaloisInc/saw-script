class Test
{
    int a;
    static int b;
    int[] c;

    int add1 (int x, int y) {
        a = x;
        return x + y;
    }

    int add2 (int x, int y) {
        b = x;
        return x + y;
    }

    int add3 (int x, int y) {
        c[1] = x;
        return x + y;
    }

    int wrap1 (int x, int y) {
        return add1 (x, y);
    }
    int wrap2 (int x, int y) {
        return add2 (x, y);
    }
    int wrap3 (int x, int y) {
        return add3 (x, y);
    }
}
