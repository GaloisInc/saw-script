class Test
{
    public static boolean addBoolean(boolean x, boolean y) {
        return x != y;
    }
    public static byte addByte(byte x, byte y) {
        return (byte) (x + y);
    }
    public static char addChar(char x, char y) {
        return (char) (x + y);
    }
    public static short addShort(short x, short y) {
        return (short) (x + y);
    }

    public static void updBoolean(boolean []a, boolean x) {
        a[0] = x;
    }
    public static void updByte(byte []a, byte x) {
        a[0] = x;
    }
    public static void updChar(char []a, char x) {
        a[0] = x;
    }
    public static void updShort(short []a, short x) {
        a[0] = x;
    }
}
