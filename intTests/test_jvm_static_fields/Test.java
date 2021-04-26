class A
{
    static long x;
    static long y;
    static void setX(long v) {
        x = v;
    }
    static void setY(long v) {
        y = v;
    }
    static long getSum() {
        return x + y;
    }
}

class B extends A
{
    static long y;
    static void setY(long v) {
        y = v;
    }
}

class C extends B
{
    static long getSum() {
        return x + y;
    }
}
