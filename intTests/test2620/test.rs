fn f(_: &[u8]) {}

pub fn g(a: [u8; 2]) {
    f(&a)
}

pub fn h(a: [u8; 5]) {
    f(&a[0..2])
}

pub fn i(a: [u8; 5]) {
    f(&a[3..5])
}

fn f_u32(_: &[u32]) {}

pub fn h_u32(a: [u32; 5]) {
    f_u32(&a[0..2])
}
