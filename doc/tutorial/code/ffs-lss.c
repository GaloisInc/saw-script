#include <stdlib.h>
#include <sym-api.h>

int ffs1(int word) {
    int i = 0;
    if(!word)
        return 0;
    for(int cnt = 0; cnt < 32; cnt++)
        if(((1 << i++) & word) != 0)
            return i;
    return 0;
}

int ffs2(int i) {
    char n = 1;
    if (!(i & 0xffff)) { n += 16; i >>= 16; }
    if (!(i & 0x00ff)) { n += 8;  i >>= 8; }
    if (!(i & 0x000f)) { n += 4;  i >>= 4; }
    if (!(i & 0x0003)) { n += 2;  i >>= 2; }
    return (i) ? (n+((i+1) & 0x01)) : 0;
}

int main() {
    int x = (int)lss_fresh_uint32(0);
    int z = ffs1(x);
    int z2 = ffs2(x);
    lss_write_aiger_uint32(z, "c_ffs_ref.aig");
    lss_write_aiger_uint32(z2, "c_ffs_imp.aig");
}
