import com.galois.symbolic.*;
class FFSAig {
    static int ffs_ref(int word) {
        int i = 0;
        if(word == 0)
            return 0;
        for(int cnt = 0; cnt < 32; cnt++)
            if(((1 << i++) & word) != 0)
                return i;
        return 0;
    }

    static int ffs(int i) {
        byte n = 1;
        if ((i & 0xffff) == 0) { n += 16; i >>= 16; } else { n = n; }
        if ((i & 0x00ff) == 0) { n +=  8; i >>=  8; } else { n = n; }
        if ((i & 0x000f) == 0) { n +=  4; i >>=  4; } else { n = n; }
        if ((i & 0x0003) == 0) { n +=  2; i >>=  2; } else { n = n; }
        if (i != 0) { return (n+((i+1) & 0x01)); } else { return 0; }
    }

    public static void main(String[] args) {
        int i = Symbolic.freshInt(0);
        int ffs_good = ffs_ref(i);
        int ffs_i = ffs(i);
        Symbolic.writeAiger("java_ffs_ref.aig", ffs_good);
        Symbolic.writeAiger("java_ffs_imp.aig", ffs_i);
    }
}
