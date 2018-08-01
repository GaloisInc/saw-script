pub fn ffs_ref(w : u32) -> u32 {
    let mut i = 0;
    let mut word = w;
    if word == 0 { return 0; }

    let mut cnt = 0;
    while cnt < 32 {
        if (1 << i) & word != 0 {
            i += 1;
            return i;
        }
        i += 1;
        cnt += 1;
    }
    0
}

pub fn ffs_imp(j : u32) -> u32 {
    let mut n : u8 = 1;
    let mut i = j;
    if (i & 0xffff) == 0 {
        n += 16; i >>= 16;
    }
    if (i & 0x00ff) == 0 {
        n += 8; i >>= 8;
    }
    if (i & 0x000f) == 0 {
        n += 4; i >>= 4;
    }
    if (i & 0x0003) == 0 {
        n += 2; i >>= 2;
    }
    if i != 0 {
        return (n as u32) + ((i + 1) & 0x01);
    }
    else {
        return 0;
    }
}

fn main() {}
