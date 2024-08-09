///// Basics

pub fn example_unsigned(x: u8) -> u16 {
    2u8.wrapping_mul(x) as u16
}

pub fn example_signed(x: i8) -> i16 {
    -2i8.wrapping_mul(x) as i16
}

pub fn example_char(x: char) -> char {
    x
}

pub fn example_bool(x: bool) -> bool {
    !x
}

pub fn example_array(x: [u32; 4]) -> [u32; 4] {
    [x[3], x[2], x[1], x[0]]
}

pub fn example_unit(x: ()) -> () {
    x
}

pub fn example_tuple(x: (u8, i16)) -> (i16, u8) {
    (x.1, x.0)
}

///// FFS

// returns the index of the first non-zero bit
pub fn ffs_ref(word: u32) -> u32 {
    let mut i: u32 = 0;
    if word == 0 {
        return 0;
    }
    for _cnt in 0..32 {
        if ((1 << i) & word) != 0 {
            i += 1;
            return i;
        } else {
            i += 1;
        }
    }
    return 0; // notreached
}

pub fn ffs_imp(mut i: u32) -> u32 {
    let mut n: u32 = 1;
    if i & 0xffff == 0 { n += 16; i >>= 16; }
    if i & 0x00ff == 0 { n += 8;  i >>= 8; }
    if i & 0x000f == 0 { n += 4;  i >>= 4; }
    if i & 0x0003 == 0 { n += 2;  i >>= 2; }
    return if i != 0 { n+((i+1) & 0x01) } else { 0 };
}

// Creative optimized version based on musl libc:
// http://www.musl-libc.org/.
//
// Apparently this is a well known approach:
// https://en.wikipedia.org/wiki/Find_first_set#CTZ. The DeBruijn
// (https://en.wikipedia.org/wiki/De_Bruijn_sequence) sequence here is
// different from the one in the Wikipedia article on 'ffs'.
pub fn ffs_musl(x: u32) -> u32 {
    static DEBRUIJN32: [u32; 32] = [
        0, 1, 23, 2, 29, 24, 19, 3, 30, 27, 25, 11, 20, 8, 4, 13,
        31, 22, 28, 18, 26, 10, 7, 12, 21, 17, 9, 6, 16, 5, 15, 14
    ];
    let x_i32 = x as i32;
    if x != 0 {
        DEBRUIJN32[(((x_i32 & -x_i32).wrapping_mul(0x076be629) as u32) >> 27) as usize]+1
    } else {
        0
    }
}

pub fn ffs_bug(word: u32) -> u32 {
    // injected bug:
    if word == 0x101010 { return 4; }
    ffs_ref(word)
}
