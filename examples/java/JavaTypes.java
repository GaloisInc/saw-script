class JavaTypes {
    boolean boolfld;
    byte    bfld;
    char    cfld;
    short   sfld;
    int     ifld;
    long    lfld;
    boolean[] boolafld;
    byte[]  bafld;
    char[]  cafld;
    short[] safld;
    int[]   iafld;
    long[]  lafld;

    void bool_set (boolean b)  { boolfld = b; }
    void byte_set (byte b)  { bfld = b; }
    void char_set (char c)  { cfld = c; }
    void short_set(short s) { sfld = s; }
    void int_set  (int i)   { ifld = i; }
    void long_set (long l)  { lfld = l; }

    void bool_aset (boolean[] ba)  { boolafld = ba; }
    void byte_aset (byte[] ba)  { bafld = ba; }
    void char_aset (char[] ca)  { cafld = ca; }
    void short_aset(short[] sa) { safld = sa; }
    void int_aset  (int[] ia)   { iafld = ia; }
    void long_aset (long[] la)  { lafld = la; }

    boolean  bool_get () { return boolfld; }
    byte  byte_get () { return bfld; }
    char  char_get () { return cfld; }
    short short_get() { return sfld; }
    int   int_get  () { return ifld; }
    long  long_get () { return lfld; }

    boolean[]  bool_aget () { return boolafld; }
    byte[]  byte_aget () { return bafld; }
    char[]  char_aget () { return cafld; }
    short[] short_aget() { return safld; }
    int[]   int_aget  () { return iafld; }
    long[]  long_aget () { return lafld; }
}
